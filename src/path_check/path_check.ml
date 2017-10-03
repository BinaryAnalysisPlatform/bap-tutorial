open Core_kernel.Std
open Bap.Std
open Graphlib.Std
open Format
include Self()

module CG = Graphs.Callgraph
module CFG = Graphs.Tid

type proof =
  | Calls of CG.edge path
  | Sites of CFG.edge path

let find_sub prog name =
  Term.enum sub_t prog |>
  Seq.find_map ~f:(fun s ->
      Option.some_if (Sub.name s = name) (Term.tid s))

let reaches cg callee target =
  Graphlib.is_reachable (module CG) cg callee target

let callsites cg target sub =
  Term.enum blk_t sub |>
  Seq.concat_map ~f:(fun blk ->
      Term.enum jmp_t blk |> Seq.filter_map ~f:(fun j ->
          match Jmp.kind j with
          | Goto _ | Ret _ | Int (_,_) -> None
          | Call dst -> match Call.target dst with
            | Direct tid when reaches cg tid target ->
              Some (Term.tid blk)
            | _ -> None))

let verify src dst prog : proof option =
  let cg = Program.to_graph prog in
  match Graphlib.shortest_path (module CG) cg src dst with
  | Some path -> Some (Calls path)
  | None ->
    Term.enum sub_t prog |> Seq.find_map ~f:(fun sub ->
        let g = Sub.to_graph sub in
        Seq.find_map (callsites cg src sub) ~f:(fun sc ->
            Seq.find_map (callsites cg dst sub) ~f:(fun dc ->
                if Tid.equal sc dc then None
                else Graphlib.shortest_path (module CFG) g sc dc))) |>
    Option.map ~f:(fun p -> Sites p)

let pp_path get_src get_dst ppf path =
  let print_node n = fprintf ppf "%s" (Tid.name n) in
  print_node (get_src (Path.start path));
  Seq.iter (Path.edges path) ~f:(fun e ->
      pp_print_string ppf " -> ";
      print_node (get_dst e))

let pp_calls = pp_path CG.Edge.src CG.Edge.dst
let pp_sites = pp_path CFG.Edge.src CFG.Edge.dst


let main src dst proj =
  let prog = Project.program proj in
  match Option.both (find_sub prog src) (find_sub prog dst) with
  | None -> printf "satisfied (trivially)@\n"
  | Some (src,dst) -> match verify src dst prog with
    | None -> printf "satisfied (no counter-example was found)\n"
    | Some p ->
      printf "unsatisfied by ";
      match p with
      | Calls p -> printf "calls via %a@\n" pp_calls p
      | Sites p -> printf "callsites via %a@\n" pp_sites p

module Cmdline = struct
  open Config
  let src = param string "src" ~doc:"Name of the source function"
  let dst = param string "dst" ~doc:"Name of the sink function"

  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' (main !!src !!dst))

  let () = manpage [
      `S "DESCRIPTION";
      `P
        "Checks whether there is an execution path that contains a call
    to the $(v,src) function before a call to the $(v,dst)
    parameter. Outputs a possible (shortest) path that can
    lead to the policy violation."
    ]
end
