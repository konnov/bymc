(* Tool options. As its number continues to grow,
   it is easier to make them accessible to other modules.

   Igor Konnov, 2013
 *)

open Str

open Accums

module StringMap = Map.Make(String)

type action_opt_t =
    OptAbstract | OptRefine | OptCheckInv | OptSubstitute | OptNone

type mc_tool_opt_t = ToolSpin | ToolNusmv

type options_t =
    {
        action: action_opt_t; trail_name: string; filename: string;
        inv_name: string; param_assignments: int StringMap.t;
        mc_tool: mc_tool_opt_t; bdd_pass: bool; verbose: bool
    }

let empty =
    { action = OptNone; trail_name = ""; filename = "";
      inv_name = ""; param_assignments = StringMap.empty;
      mc_tool = ToolSpin; bdd_pass = false; verbose = false; }

let parse_key_values str =
    let parse_pair map s =
        if string_match (regexp "\\([a-zA-Z0-9]+\\)=\\([0-9]+\\)") s 0
        then StringMap.add (matched_group 1 s) (int_of_string (matched_group 2 s)) map
        else raise (Arg.Bad ("Wrong key=value pair: " ^ s))
    in
    let pairs = split (regexp ",") str in
    List.fold_left parse_pair StringMap.empty pairs


let parse_options =
    let opts = ref {
        action = OptNone; trail_name = ""; filename = ""; inv_name = "";
        param_assignments = StringMap.empty; bdd_pass = false;
        mc_tool = ToolSpin; verbose = false
    } in
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
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "produce lots of verbose output (you are warned).");
        ]
        (fun s -> if !opts.filename = "" then opts := {!opts with filename = s})
        "Use: bymc [options] promela_file");

    !opts

