open Printf

open Accums
open Debug
open PiaDom
open Plugin
open SpinIr
open SpinIrImp

class pia_dom_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        val mutable m_dom: pia_domain option =  None

        method transform rt =
            let prog = self#get_input0 in
            let roles = rt#caches#analysis#get_var_roles prog in
            let pxz = (self#has_opt rt "pxz02")
                && (self#get_opt rt "pxz02") <> "0" in
            if pxz
            then begin
                m_dom <- Some (new pia_domain [IntConst 0; IntConst 1; IntConst 2]);
                log INFO "   forced (0, 1, \\infty) by Pnueli, Xu, Zuck 2002"
            end else if self#has_opt rt "thresholds"
            then begin
                let ts =
                    self#parse_thresholds prog (self#get_opt rt "thresholds") in
                let ts_s = str_join ", " (List.map expr_s ts) in
                log INFO (sprintf "   forced the thresholds: [%s]" ts_s);
                m_dom <- Some (new pia_domain ts)
            end else m_dom <- Some (create rt#solver roles prog);
            prog

        method update_runtime rt =
            match m_dom with
            | Some d -> rt#caches#analysis#set_pia_dom d
            | _ -> ()

        method parse_thresholds prog thr_s =
            let tss = Str.split (Str.regexp_string ",") thr_s in
            List.map (Parse.parse_expr (Program.get_sym_tab prog)) tss
    end

