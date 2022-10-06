include "mexpr/ast-builder.mc"
include "mexpr/externals.mc"
include "mexpr/boot-parser.mc"
include "mexpr/type.mc"
include "sys.mc"
include "map.mc"

include "../coreppl.mc"
include "../inference-common/smc.mc"
include "../parser.mc"
include "../dppl-arg.mc"
include "../src-location.mc"

-- Inference methods
include "apf/compile.mc"
include "bpf/compile.mc"
include "importance/compile.mc"
include "mcmc-naive/compile.mc"
include "mcmc-trace/compile.mc"
include "mcmc-lightweight/compile.mc"

let parseRuntime = use BootParser in lam runtime. parseMCoreFile {
  defaultBootParserParseMCoreFileArg with
    eliminateDeadCode = false,
    allowFree = true
  } (join [corepplSrcLoc, "/coreppl-to-mexpr/", runtime])

-- NOTE(dlunde,2022-05-04): No way to distinguish between CorePPL and MExpr AST
-- types here. Optimally, the type would be Options -> CorePPLExpr -> MExprExpr
-- or similar.
lang MExprCompile =
  MExprPPL + Resample + Externals + MExprANFAll + MExprPPLCFA

  sem _replaceHigherOrderConstant: Const -> Option Expr
  sem _replaceHigherOrderConstant =
  | CMap _ -> Some (var_ "map")
  | CMapi _ -> Some (var_ "mapi")
  | CIter _ -> Some (var_ "iter")
  | CIteri _ -> Some (var_ "iteri")
  | CFoldl _ -> Some (var_ "foldl")
  | CFoldr _ -> Some (var_ "foldr")
  | CCreate _ -> Some (var_ "create")
  | _ -> None ()

  sem _replaceHigherOrderConstantExpr: Expr -> Expr
  sem _replaceHigherOrderConstantExpr =
  | TmConst r ->
    match _replaceHigherOrderConstant r.val with Some t then
      withType r.ty (withInfo r.info t)
    else TmConst r
  | t -> t

  sem replaceHigherOrderConstants: Expr -> Expr
  sem replaceHigherOrderConstants =
  | t ->
    let t = mapPre_Expr_Expr _replaceHigherOrderConstantExpr t in
    let replacements = parseRuntime "runtime-const.mc" in
    let replacements = normalizeTerm replacements in
    let t = bind_ replacements t in
    let t = symbolizeExpr
      { symEnvEmpty with allowFree = true, ignoreExternals = true } t
    in
    t

  sem desymbolizeExternals =
  | prog ->
    recursive let rec = lam env. lam prog.
      match prog with TmExt ({ ident = ident, inexpr = inexpr } & b) then
        let noSymIdent = nameNoSym (nameGetStr ident) in
        let env =
          if nameHasSym ident then (mapInsert ident noSymIdent env) else env
        in
        TmExt { b with ident = noSymIdent, inexpr = rec env inexpr }
      else match prog with TmVar ({ ident = ident } & b) then
        let ident =
          match mapLookup ident env with Some ident then ident else ident in
        TmVar { b with ident = ident }
      else smap_Expr_Expr (rec env) prog
    in rec (mapEmpty nameCmp) prog

end

let mexprCompile: Options -> Expr -> Expr =
  use MExprCompile in
  lam options. lam prog.

    -- Load runtime and compile function
    let compiler: (String, (Expr,Expr) -> Expr) =
      switch options.method
        case "mexpr-apf" then compilerAPF options
        case "mexpr-bpf" then compilerBPF options
        case "mexpr-importance" then compilerImportance options
        case "mexpr-mcmc-naive" then compilerNaiveMCMC options
        case "mexpr-mcmc-trace" then compilerTraceMCMC options
        case "mexpr-mcmc-lightweight" then compilerLightweightMCMC options
        case _ then error (
          join [ "Unknown CorePPL to MExpr inference method:", options.method ]
        )
      end
    in

    match compiler with (runtime, compile) in

    -- Type check model. NOTE(dlunde,2022-06-09): We do not want the
    -- annotations added by the type checker, as this may make the printed
    -- program unparsable. That's why we simply discard the result here (but,
    -- we first extract the return type).
    let tcprog = typeCheck prog in
    let resTy = tyTm tcprog in

    -- Symbolize model (ignore free variables and externals)
    let prog = symbolizeExpr
      { symEnvEmpty with allowFree = true, ignoreExternals = true } prog
    in

    -- Desymbolize externals in case any were symbolized beforehand
    let prog = desymbolizeExternals prog in

    -- ANF transformation
    let prog = normalizeTerm prog in

    -- ANF with higher-order intrinsics replaced with alternatives in
    -- seq-native.mc
    let progNoHigherOrderConstants = replaceHigherOrderConstants prog in

    -- Apply inference-specific transformation
    let prog = compile (prog, progNoHigherOrderConstants) in

    -- Parse inference runtime
    let runtime = parseRuntime runtime in

    -- Get external definitions from runtime-AST (input to next step)
    let externals = getExternalIds runtime in

    -- Remove duplicate external definitions in model (already included in the
    -- runtime)
    let prog = removeExternalDefs externals prog in

    -- Put model in top-level model function and extract deterministic definitions
    let prog = (ulet_ "model" (lams_ [("state", tycon_ "State")] prog)) in

    -- Construct record accessible in runtime
    -- NOTE(dlunde,2022-06-28): It would be nice if we automatically lift the
    -- options variable here to an Expr.
    let pre = ulet_ "compileOptions" (urecord_ [
      ("resample", str_ options.resample),
      ("cps", str_ options.cps),
      ("printSamples", bool_ options.printSamples),
      ("earlyStop", bool_ options.earlyStop),
      ("mcmcLightweightGlobalProb", float_ options.mcmcLightweightGlobalProb),
      ("printAcceptanceRate", bool_ options.printAcceptanceRate)
    ]) in

    -- Printing function for return type
    let tyPrintFun =
    let errMsg = "Return type cannot be printed" in
      match resTy with TyInt _ then (var_ "int2string")
      else match resTy with TyFloat _ then uconst_ (CFloat2string ())
      else match resTy with TyBool _ then (var_ "bool2string")
      else match resTy with TySeq { ty = TyChar _ } then (ulam_ "x" (var_ "x"))
      else match resTy with TyChar _ then (ulam_ "x" (seq_ [(var_ "x")]))
      else match resTy with TyRecord r then
        if mapIsEmpty r.fields then (ulam_ "x" (str_ "()"))
        else error errMsg
      else error errMsg
    in

    let post = bindall_ [
      ulet_ "printFun" (app_ (var_ "printRes") tyPrintFun),
      appf2_ (var_ "run") (var_ "model") (var_ "printFun")
    ] in

    -- Combine runtime, model, and generated post
    let prog = bindall_ [pre,runtime,prog,post] in

    if options.debugMExprCompile then
      -- Check that the combined program type checks
      typeCheck prog
    else ();

    -- Return complete program
    prog

mexpr

let parse = parseMExprPPLString in

let simple = parse "
let x = assume (Beta 10.0 5.0) in
let obs = true in
observe obs (Bernoulli x);
x
" in

-- Simple tests that ensure compilation throws no errors
utest mexprCompile {default with method = "mexpr-apf"} simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-bpf"} simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-importance", cps = "none" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-importance", cps = "partial" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-importance", cps = "full" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-mcmc-naive" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-mcmc-trace" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-mcmc-lightweight" } simple
with () using lam. lam. true in
utest mexprCompile {default with method = "mexpr-mcmc-lightweight", align = true } simple
with () using lam. lam. true in

()
