(* Tool options. As the number of options continues to grow,
   this is one place to check the options and to access them from other modules.

   Igor Konnov, 2013-2015
 *)

open Str

open Accums

let version = [0; 9; 7]
let version_full = "ByMC-1.1.0-feature-CAV16-liveness"

let macro_prefix = "macro."

type action_opt_t =
    | OptAbstract | OptRefine | OptVersion | OptNone

type mc_tool_opt_t = ToolSpin | ToolNusmv | ToolNone

type smt_opt_t = SmtYices | SmtLib2 of string array | SmtMathsat5

type options_t =
    {
        action: action_opt_t;
        trail_name: string;
        filename: string;
        spec: string;
        chain: string;
        param_assignments: int StrMap.t;
        mc_tool: mc_tool_opt_t;
        smt: smt_opt_t;
        bdd_pass: bool;
        verbose: bool;
        plugin_opts: string StrMap.t;
        plugin_dir: string;
    }

let empty = {
    action = OptNone; trail_name = ""; filename = ""; spec = "";
    chain = "piaDataCtr";
    param_assignments = StrMap.empty;
    mc_tool = ToolSpin; bdd_pass = false; verbose = false;
    smt = SmtYices;
    plugin_opts = StrMap.empty;
    plugin_dir = ""
}


let get_plugin_opt opts name =
    try Some (StrMap.find name opts.plugin_opts)
    with Not_found -> None


let parse_key_values str =
    let parse_pair map s =
        if string_match (regexp "\\([a-zA-Z0-9]+\\)=\\([0-9]+\\)") s 0
        then StrMap.add (matched_group 1 s) (int_of_string (matched_group 2 s)) map
        else raise (Arg.Bad ("Wrong key=value pair: " ^ s))
    in
    let pairs = split (regexp ",") str in
    List.fold_left parse_pair StrMap.empty pairs


let parse_plugin_opt str =
    let re = regexp "\\([_a-zA-Z0-9]+\\.[_a-zA-Z0-9]+\\) *= *\\(.*\\)" in
    if string_match re str 0
    then (matched_group 1 str, matched_group 2 str)
    else raise (Arg.Bad ("Syntax for plugin options: plugin.attr=val"))


let parse_mc_tool = function
    | "spin" -> ToolSpin
    | "nusmv" -> ToolNusmv
    | "none" -> ToolNone
    | _ as s -> raise (Failure ("Unknown option: " ^ s))


let parse_smt s =
    if s = "yices"
    then SmtYices
    else if s = "mathsat5"
    then SmtMathsat5
    else begin
        try
            if "lib2|" = (Str.string_before s 5)
            then let cmd = Str.string_after s 5 in  
                SmtLib2 (Array.of_list (Str.split_delim (Str.regexp "|") cmd))
            else raise (Failure ("Unknown --smt argument: " ^ s))
        with Invalid_argument _ ->
            raise (Failure ("Unknown --smt argument: " ^ s))
    end


let parse_options _ =
    let opts = ref {empty with filename = ""} in
    let specs = [
            ("--chain", (Arg.Symbol (["piaDataCtr"; "concrete"; "bounds"; "post"; "fast"; "skelSmv"],
                (fun s -> opts := {!opts with chain = s}))),
                " choose a transformation/refinement chain (default: piaDataCtr)."
            );
            ("-a", Arg.Unit (fun () -> opts := {!opts with action = OptAbstract}),
             "apply a transformation chain (see --chain).");
            ("-t", Arg.String
             (fun s -> opts := {!opts with action = OptRefine; trail_name = s}),
             "try to refine a program produced before (using a counterexample).");
            (* TODO: get rid of it,
                it should fit into the standard chain workflow *)
            ("-s", Arg.String (fun s ->
                opts := {!opts with action = OptAbstract;
                    chain = "concrete";
                    param_assignments = parse_key_values s}),
             "substitute parameters into the code and produce standard Promela.");
            ("--target", (Arg.Symbol (["spin"; "nusmv"; "none"],
                (fun s -> opts := {!opts with mc_tool = parse_mc_tool s}))),
                " choose a model checker from the list (default: spin)."
            );
            ("--smt", (Arg.String (fun s ->
                opts := {!opts with smt = parse_smt s})),
                " choose SMT solver: yices (default), lib2|solver-name|arg1|arg2...");
            ("--spec", (Arg.String (fun s -> opts := {!opts with spec = s})),
                " specification name to check."
            );
            ("-O", Arg.String (fun s ->
                let name, value = parse_plugin_opt s in
                opts := {!opts with plugin_opts =
                    (StrMap.add name value !opts.plugin_opts); }
                ),
             "P.X=Y set option X of plugin P to Y.");
            ("-D", Arg.String (fun s ->
                let name, value = parse_plugin_opt (macro_prefix ^ s) in
                opts := {!opts with plugin_opts =
                    (StrMap.add name value !opts.plugin_opts); }
                ),
             "X=Y define a C-like macro X as Y.");
            ("--plugin-dir",
                Arg.String (fun plugin_dir -> opts := {!opts with plugin_dir }),
             "directory, where the plugins are stored.");
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "produce lots of verbose output (you are warned).");
            ("--version", Arg.Unit
                (fun _ -> opts := {!opts with action = OptVersion }),
             "print version number.");
        ]
    in
    let anon_fun s =
        if !opts.filename = ""
        then opts := { !opts with filename = s }
    in
    let usage_msg = "Use: bymc [options] promela_file"
    in
    Arg.parse specs anon_fun usage_msg;
    !opts

