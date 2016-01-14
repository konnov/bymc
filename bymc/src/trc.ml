(* Tracing codes (see Debug.trace).
 * The codes MUST be short, as they are used as the keys in
 * a hash table.
 *
 * Do not open this module, as it will pollute the name space,
 * but use the full name, e.g., Trc.SMT.
 *
 * Pass -O trace.mods=mod1,mod2 to enable tracing in a specific module.
 *
 * Igor Konnov 2013-2014
 *)

let smt = "SMT" (* smt *)
let ssa = "SSA" (* ssa *)
let cmd = "CMD" (* pipeCmd *)
let nse = "NSE" (* nusmvSsaEncoding *)
let pcr = "PCR" (* piaCtrRefinement *)
let exe = "EXE" (* symbExec *)
let bnd = "BND" (* porBounds *)
let sum = "SUM" (* summary *)
let cfg = "CFG" (* cfg *)
let ssk = "SSK" (* symbSkel *)
let pos = "POS" (* poset *)
let scl = "SCL" (* schemaCheckerLtl *)

