(* Tool options. As its number continues to grow,
   it is easier to make them accessible to other modules.

   Igor Konnov, 2013
 *)

open Str

open Accums

module StringMap = Map.Make(String)

let version = [0; 3; 1]
let version_full = "ByMC-0.3.1-dev"

type action_opt_t =
    | OptAbstract | OptRefine | OptSubstitute | OptNone

type mc_tool_opt_t = ToolSpin | ToolNusmv

type options_t =
    {
        action: action_opt_t; trail_name: string; filename: string;
        inv_name: string; param_assignments: int StringMap.t;
        mc_tool: mc_tool_opt_t; bdd_pass: bool; verbose: bool;
        plugin_opts: string StringMap.t
    }

let empty =
    { action = OptNone; trail_name = ""; filename = "";
      inv_name = ""; param_assignments = StringMap.empty;
      mc_tool = ToolSpin; bdd_pass = false; verbose = false;
      plugin_opts = StringMap.empty
    }


let parse_key_values str =
    let parse_pair map s =
        if string_match (regexp "\\([a-zA-Z0-9]+\\)=\\([0-9]+\\)") s 0
        then StringMap.add (matched_group 1 s) (int_of_string (matched_group 2 s)) map
        else raise (Arg.Bad ("Wrong key=value pair: " ^ s))
    in
    let pairs = split (regexp ",") str in
    List.fold_left parse_pair StringMap.empty pairs


let parse_plugin_opt str =
    let re = regexp "\\([a-zA-Z0-9]+\\.[a-zA-Z0-9]+\\) *= *\\(.*\\)" in
    if string_match re str 0
    then (matched_group 1 str, matched_group 2 str)
    else raise (Arg.Bad ("Syntax for plugin options: plugin.attr=val"))


let parse_options =
    let opts = ref {empty with filename = ""} in
    let parse_mc_tool = function
    | "spin" -> ToolSpin
    | "nusmv" -> ToolNusmv
    | _ as s -> raise (Failure ("Unknown option: " ^ s))
    in
    (Arg.parse
        [
            ("-a", Arg.Unit (fun () -> opts := {!opts with action = OptAbstract}),
             "produce the counter abstraction of a Promela program.");
            ("-t", Arg.String
             (fun s -> opts := {!opts with action = OptRefine; trail_name = s}),
             "check feasibility of a counterexample produced by spin -t (not a *.trail!).");
            ("-s", Arg.String (fun s ->
                opts := {!opts with action = OptSubstitute;
                    param_assignments = parse_key_values s}),
             "substitute parameters into the code and produce standard Promela.");
            ("--target", (Arg.Symbol (["spin"; "nusmv"],
                (fun s -> opts := {!opts with mc_tool = (parse_mc_tool s)}))),
                " choose a model checker from the list (default: spin)."
            );
            ("-O", Arg.String (fun s ->
                let name, value = parse_plugin_opt s in
                opts := {!opts with plugin_opts =
                    (StringMap.add name value !opts.plugin_opts); }
                ),
             "P.X=Y set option X of plugin P to Z.");
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "produce lots of verbose output (you are warned).");
        ]
        (fun s ->
            if !opts.filename = ""
            then opts := {!opts with filename = s})
        "Use: bymc [options] promela_file");

    !opts

