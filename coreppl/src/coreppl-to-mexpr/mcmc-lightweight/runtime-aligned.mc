include "common.mc"

include "ext/dist-ext.mc"
include "ext/math-ext.mc"
include "math.mc"
include "seq.mc"
include "string.mc"
include "option.mc"

include "../runtime-common.mc"
include "../runtime-dists.mc"

-- Any-type, used for traces
type Any = ()


-- In aligned MCMC, the state is the accumulated weight, samples, and samples to
-- reuse.
type State = {

  -- The weight of the current execution
  weight: Ref Float,

  -- The weight of reused values in the previous and current executions
  weightReusedPrev: Ref Float,
  weightReused: Ref Float,

  -- The aligned trace for this execution
  alignedTrace: Ref [(Any, Float)],

  -- Number of encountered assumes (unaligned and aligned)
  traceLength: Ref Int,

  -- The previous aligned trace, with potentially invalidated samples
  oldAlignedTrace: Ref [Option (Any,Float)],

  -- Aligned trace length (a constant, determined at the first run)
  alignedTraceLength: Ref Int

}

-- NOTE(dlunde,2022-05-23): The below implementation does not
-- work with ropes for some reason (segfaults). We must therefore use lists.
let emptyList = toList []

-- State (reused throughout inference)
let state: State = {
  weight = ref 0.,
  weightReusedPrev = ref 0.,
  weightReused = ref 0.,
  alignedTrace = ref emptyList,
  traceLength = ref 0,
  oldAlignedTrace = ref emptyList,
  alignedTraceLength = ref (negi 1)
}

let updateWeight = lam v.
  modref state.weight (addf (deref state.weight) v)

let incrTraceLength: () -> () = lam.
  modref state.traceLength (addi (deref state.traceLength) 1)

-- Procedure at aligned samples
let sampleAligned: all a. Dist a -> a = lam dist.
  let oldAlignedTrace: [Option (Any,Float)] = deref state.oldAlignedTrace in
  let newSample: () -> (Any,Float) = lam.
    let s = dist.sample () in
    let w = dist.logObserve s in
    (unsafeCoerce s, w)
  in
  let sample: (Any, Float) =
    match oldAlignedTrace with [sample] ++ oldAlignedTrace then
      modref state.oldAlignedTrace oldAlignedTrace;
      match sample with Some (sample,w) then
        -- printLn (join [
        --   "ALIGNED: Aligned _reused_ sample, index ",
        --   int2string (subi (deref state.alignedTraceLength) (length oldAlignedTrace))
        -- ]);
        let s: a = unsafeCoerce sample in
        let wNew = dist.logObserve s in
        modref state.weightReused (addf (deref state.weightReused) wNew);
        modref state.weightReusedPrev (addf (deref state.weightReusedPrev) w);
        (sample, wNew)
      else
        -- printLn (join [
        --   "ALIGNED: Aligned _new_ sample, index ",
        --   int2string (subi (deref state.alignedTraceLength) (length oldAlignedTrace))
        -- ]);
        newSample ()

    -- This case should only happen in the first run when there is no previous
    -- aligned trace
    else
      -- printLn (join [
      --   "ALIGNED: Aligned _new_ sample, index ",
      --   int2string (subi (deref state.alignedTraceLength) (length oldAlignedTrace))
      -- ]);
      newSample ()

  in
  incrTraceLength ();
  modref state.alignedTrace (cons sample (deref state.alignedTrace));
  unsafeCoerce (sample.0)

let sampleUnaligned: all a. Dist a -> a = lam dist.
  -- printLn "ALIGNED: Unaligned sample, should never happen for this model";
  incrTraceLength ();
  dist.sample ()

-- Function to propose aligned trace changes between MH iterations.
let modTrace: () -> () = lam.

  let alignedTraceLength: Int = deref state.alignedTraceLength in

  recursive let rec: Int -> [(Any,Float)] -> [Option (Any,Float)]
                       -> [Option (Any,Float)] =
    lam i. lam samples. lam acc.
      match samples with [sample] ++ samples then
        -- Invalidate sample if it has the invalid index
        let acc: [Option (Any, Float)] =
          cons (if eqi i 0 then None () else Some sample) acc in
        rec (subi i 1) samples acc

      else acc
  in

  -- Enable global modifications with probability gProb
  let gProb = compileOptions.mcmcLightweightGlobalProb in
  let modGlobal: Bool = bernoulliSample gProb in

  if modGlobal then
    modref state.oldAlignedTrace (map (lam. None ()) (deref state.alignedTrace))
  else
    -- One index must always change
    let invalidIndex: Int = uniformDiscreteSample 0 (subi alignedTraceLength 1) in
    modref state.oldAlignedTrace
      (rec invalidIndex (deref state.alignedTrace) emptyList)


-- General inference algorithm for aligned MCMC
let run : all a. (State -> a) -> (Res a -> ()) -> () = lam model. lam printResFun.

  -- Read number of runs and sweeps
  match monteCarloArgs () with (runs, sweeps) in

  recursive let mh : [Float] -> [a] -> Int -> ([Float], [a]) =
    lam weights. lam samples. lam iter.
      if leqi iter 0 then (weights, samples)
      else
        let prevAlignedTrace = deref state.alignedTrace in
        let prevSample = head samples in
        let prevTraceLength = deref state.traceLength in
        let prevWeight = head weights in
        modTrace ();
        modref state.weight 0.;
        modref state.weightReused 0.;
        modref state.weightReusedPrev 0.;
        modref state.alignedTrace emptyList;
        modref state.traceLength 0;
        let sample = model state in
        -- printLn "--------------";
        let traceLength = deref state.traceLength in
        let weight = deref state.weight in
        let weightReused = deref state.weightReused in
        let weightReusedPrev = deref state.weightReusedPrev in
        let logMhAcceptProb =
          minf 0. (addf -- (addf
                    (subf weight prevWeight)
                    (subf weightReused weightReusedPrev))
                    -- This part is actually wrong for aligned. The random draw to change is selected between the aligned draws, which there are a constant number of in each execution.
                    -- (subf (log (int2float prevTraceLength))
                    --           (log (int2float traceLength)))
                    -- )
        in
        -- print "logMhAcceptProb: "; printLn (float2string logMhAcceptProb);
        -- print "weight: "; printLn (float2string weight);
        -- print "prevWeight: "; printLn (float2string prevWeight);
        -- print "weightReused: "; printLn (float2string weightReused);
        -- print "weightReusedPrev: "; printLn (float2string weightReusedPrev);
        -- print "prevTraceLength: "; printLn (float2string (int2float prevTraceLength));
        -- print "traceLength: "; printLn (float2string (int2float traceLength));
        let iter = subi iter 1 in
        if bernoulliSample (exp logMhAcceptProb) then
          mcmcAccept ();
          mh
            (cons weight weights)
            (cons sample samples)
            iter
        else
          -- NOTE(dlunde,2022-10-06): VERY IMPORTANT: Restore previous aligned
          -- trace as we reject and reuse the old sample.
          modref state.alignedTrace prevAlignedTrace;
          mh
            (cons prevWeight weights)
            (cons prevSample samples)
            iter
  in

  -- Repeat once for each sweep
  repeat (lam.

      -- Used to keep track of acceptance ratio
      mcmcAcceptInit runs;

      -- First sample
      let sample = model state in
      -- NOTE(dlunde,2022-08-22): Are the weights really meaningful beyond
      -- computing the MH acceptance ratio?
      let weight = deref state.weight in
      let iter = subi runs 1 in

      -- Set aligned trace length (a constant, only modified here)
      modref state.alignedTraceLength (length (deref state.alignedTrace));

      -- Sample the rest
      -- printLn "--------------";
      let res = mh [weight] [sample] iter in

      -- Reverse to get the correct order
      let res = match res with (weights,samples) in
        (reverse weights, reverse samples)
      in

      -- Print
      printResFun res

    ) sweeps

let printRes : all a. (a -> String) -> Res a -> () = lam printFun. lam res.
  -- NOTE(dlunde,2022-05-23): I don't think printing the norm. const makes
  -- sense for MCMC
  -- printLn (float2string (normConstant res.0));
  (if compileOptions.printAcceptanceRate then
    printLn (float2string (mcmcAcceptRate ()))
  else ());
  printSamples printFun (mapReverse (lam. 0.) res.0) res.1
