(*
 * When translating one program to another, it is sometimes useful
 * to translate expressions and variables back to the original source.
 *)

open Spin
open SpinIr
open SpinIrImp

exception NoReverseError of int

class retrans_tab =
    object(self)
        val mutable m_tab: (int, token expr) Hashtbl.t = Hashtbl.create 10

        method bind (v: var) (exp: token expr) =
            Hashtbl.replace m_tab v#id exp

        method get (v: var) =
            let id = v#id in
            if Hashtbl.mem m_tab id
            then Hashtbl.find m_tab id
            else raise (NoReverseError id)
    end

