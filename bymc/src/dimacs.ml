open Accums

let read_problem_head filename = 
    let fin = open_in filename in
    let stop = ref false in
    let n_vars = ref 0 in
    let n_clauses = ref 0 in
    while not !stop do
      let c = input_char fin in
      match c with
        'c' -> let _ = input_line fin in ()
      | 'p' ->
            Scanf.fscanf fin " cnf " ();
            Scanf.fscanf fin "%d " (fun n -> n_vars := n);
            Scanf.fscanf fin "%d " (fun n -> n_clauses := n);
            stop := true
      | '\n' -> ()
      (* anything else *)
      | _ -> Printf.printf "Unexpected command: '%c'\n" c;
            stop := true;
    done;
    (!n_vars, !n_clauses)


let scan_valuation fin threshold_id =
    let read_num () =
        let stop = ref false in
        let skip = ref true in
        let num = ref 0 in
        let sign = ref false in
        while not !stop do
            let c = input_char fin in
            match c with
                'v' -> () (* skip this *)
              | '0'..'9' ->
                    num := 10 * !num + (int_of_char c) - (int_of_char '0');
                    skip := false (* don't skip spaces anymore *)
              | '-' -> sign := true
              | ' ' -> stop := not !skip
              | '\n' -> stop := not !skip
              | '\t' -> stop := not !skip
              | _ -> raise (Failure (Printf.sprintf "Unexpected char: %c" c))
        done;
        if !sign then -(!num) else !num
    in
    let values = ref [] in
    let stop = ref false in
    while not !stop do
        let n = read_num () in
        stop := (n = 0);
        (* cut-off anything above the threshold *)
        (*Printf.printf "%d " n;*)
        if n != 0 && n <= threshold_id && n >= -threshold_id
        then values := n :: !values
    done;
    !values



let valuation_as_set valuation =
    List.fold_left
        (fun s i -> if i >= 0 then IntSet.add i s else s)
        IntSet.empty
        valuation


let read_sat_result filename threshold_id = 
    let fin = open_in filename in
    let stop = ref false in
    let values = ref [] in
    while not !stop do
      let c = input_char fin in
      match c with
        'c' -> let _ = input_line fin in ()
      | 's' -> let s = input_line fin in
            Printf.printf "%s\n" s;
            stop := (s = "UNSATISFIABLE")
      | 'v' ->
            values := (List.rev_append !values (scan_valuation fin threshold_id));
            stop := true;
      | '\n' -> ()
      (* MiniSat compatibility: 'SAT', 'UNSAT', 'INDETERMINATE' *)
      | 'I'  -> let s = input_line fin in
            Printf.printf "I%s\n" s;
            stop := (s = "NDETERMINATE")
      | 'U'  -> let s = input_line fin in
            Printf.printf "U%s\n" s;
            stop := (s = "NSAT")
      | 'S'  -> let s = input_line fin in
            Printf.printf "S%s\n" s;
            values := (List.rev_append !values
                (scan_valuation fin threshold_id));
            stop := true;
      (* anything else *)
      | _ -> Printf.printf "Unexpected command: '%c'\n" c;
            stop := true;
    done;
    !values
;;


let read_vars filename = 
    let vars_f = (open_in filename) in
    let var_list = ((Marshal.from_channel vars_f) : ((int * string) list)) in
    let (vars, max_id) =
        (List.fold_left
            (fun (v, m) (id, name) -> (IntMap.add id name v, max m id))
            (IntMap.empty, 0)
            var_list)
    in
    let local_list = ((Marshal.from_channel vars_f) : ((int * string) list)) in
    let local_map = (List.fold_left
        (fun v (id, name) -> (IntMap.add id name v))
        IntMap.empty local_list) in
    close_in vars_f;

    (vars, max_id, local_map)


let read_vars_and_valuation filename =
    let (vars, threshold_id, local_map) = read_vars "problem.vars" in    
    let valuation = (read_sat_result filename threshold_id) in
    (vars, local_map, valuation)


