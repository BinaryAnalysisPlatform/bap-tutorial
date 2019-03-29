BAP Tutorial
============

## Introduction

In this tutorial we will develop a non-trivial plugin that will verify
that in a program a certain sequence of calls doesn't happen. We will
develop the analysis in both OCaml and Python. You can choose either
path, or even both paths.

## Takeaways

By passing this tutorial you will learn how to use BAP basic
capabilities and how to extend BAP using our plugin system. You will
learn how to examine programs, by looking into their intermediate
representations (IR) or disassembly. You will also learn how to run
binaries in the emulated environment.

### OCaml Path Takeaways

1. how to build and install plugins
2. how to use command line arguments in a plugin
3. how to work with IR and different graph representations.

### Python Path Takeaways

1. how to interact with bap from the Python universe
2. how to use IR visitors
3. how to create graphs


## Preparation

To complete the OCaml path of the tutorial you will need an OCaml
development environment, bap, and all the necessary libraries. We have
prepared a Vagrantfile, that will setup your virtual machine using
Vagrant. If you have `vagrant` installed on your machine the following
will setup and prepare the necessary development environment.

```
wget http://tiny.cc/Vagrantfile
vagrant up
vagrant ssh
```

The last command will ssh you into the installed virtual machine, that
has BAP and all the necessary libraries readily available. It also
have Emacs preinstalled and configured to work with OCaml.

If you're going to take only the Python part of the tutorial and do
not want to install any virtual machines, then you can use BAP's
binary distribution. If you're using some Debian derivative, then the
following will install BAP on your system.

```
wget https://github.com/BinaryAnalysisPlatform/bap/releases/download/v1.3.0/{bap,libbap,libbap-dev}_1.3.0.deb
sudo dpkg -i {bap,libbap,libbap-dev}_1.3.0.deb
sudo install pip
sudo pip install bap networkx
```


## First Steps

For OCaml, create a new folder somewhere in your home folder, and
enter into it, e.g.,

```
mkdir check_path
cd check_path
```

Then use Emacs to create an empty file

```
emacs check_path.ml
```

Note: it is mandatory to develop each BAP plugin in a separate
folder.

After Emacs has started, use `M-x merlin-use <RET> bap` command to tell
[Merlin][1] that you're going to use the `bap` library. See [our wiki][2] for more
instructions about Merlin.


If you're developing in Python then do the same but create a file with
the `'.py` extension, e.g.,

```
emacs check_path.py
```

[1]: https://github.com/ocaml/merlin
[2]: https://github.com/BinaryAnalysisPlatform/bap/wiki/Emacs#configuring-merlin


## First steps with bap

We will need some binary to play with. For the purpose of this
tutorial, we created a special binary that is small, but still
non-trivial. You can get it using `wget`

```
wget tiny.cc/bap-echo -O exe
```

If you're running on an x86 machine you can run the binary by

```
chmod a+x exe
./exe
```

The binary will parse and print some verses from Shakespeare. It will
also echo all passed arguments.

You can also run the binary using `bap`. The binary will not be
run on an actual CPU, but emulated using the Primus Framework.

To get the disassembly of the executable use `-dasm` option, e.g.,

```
bap ./exe -dasm
```

To get the IR just use the `-d` option, e.g.,

```
bap ./exe -d
```

You can also use `-dcfg` to get the control-flow graphs, and
`-dcallgraph` to dump the program call graph. To get the full list of
supported formats use the `--list-formats` option, e.g.,

```
bap --list-formats
adt          (1.0.0)          print program IR in ADT format
asm          (1.0.0)          print assembly instructions
asm.adt      (1.0.0)          print assembly instruction endcoded in ADT format
asm.decoded  (1.0.0)          print assembly instructions as it was decoded
asm.sexp     (1.0.0)          print assembly instructions as it was decoded
bil          (1.0.0)          print BIL instructions
bil.adt      (1.0.0)          print BIL instructions in ADT format
bil.sexp     (1.0.0)          print BIL instructions in Sexp format
bir          (1.0.0)          print program in IR
callgraph    (1.0.0)          print program callgraph in DOT format
cfg          (1.0.0)          print rich CFG for each procedure
marshal      (1.0.0)          OCaml standard marshaling format
symbols      (1.0.0)          print symbol table
```

For more options see `bap --help`. For options specific to a plugin
`<PLUGIN>` use `bap --<PLUGIN>-help`, for example, the `run` plugin
help page is available via `bap --run-help`.

ProTip: if you have a GUI setup, then you can use `xdot` for interactive
visualization of control flow graphs:
```sh
bap exe -dcfg --print-symbol=main | xdot
```

## Theoretical Background

The purpose of our analysis is to verify that for all execution paths
in a program a call to the function `f` is not followed by a call to
the function `g`, where `f` and `g` are specified by a user. We can
express this property concisely using Linear Temporal Logic:

    f -> G not(g)

where `f` and `g` are propositions that are true if a call to a
the corresponding function occurred, and `G x` is the LTL operator that
requires the predicate `x` to be true on the entire subsequent path.

We will write a policy checker, that will verify that this property
holds for all execution paths, or will provide a counter-example,
proving the opposite. The checker will be static and sound (wrt to the
soundness of the CFG).

Now, let's figure out how we will prove this property:

1. If there are no calls to `f` or to `g` or to both, then the
   verification property is trivially true, i.e., `not f \/ not g`
   This property has a strong "must" modality. Since the call indeed can't happen,
   so the property `must` hold for all paths.

2. If `f` calls `g`, either directly or by calling a function that
   calls `g`, then `f` occurs before `g`. The call to `g` still may not occur,
   as we ignore path constraints, so this gives us the may modality.
   We will express this as `calls(f,g)`.

3. If there is a subroutine that has two calls that lead to `f` and `g`
   correspondingly, and these calls are reachable in the control flow graph
   of the subroutine, then `g` may be called after `f` with the may modality.
   (Again, we do not consider the feasibility of the path constraint).
   More formally, this property can be expressed as:


        sites(p,q) := calls(p,f) /\ calls(q,g) /\ reaches(p,q)

   where `reaches(x,y)` is true if there exists a control flow graph with
   a path between `x` and `y.

To summarize, in order to prove that `f -> G not(g)` holds for the static model of our program,
we need to prove that the following doesn't hold

    f /\ g \/ calls(f,g) \/ ∃p∃q, sites(p,q)





## OCaml implementation

### Boilerplate Code

We will start with several `open` and `include` statements that will
prepare our development context. Add the following to the top of the
`check_path.ml` file.

```ocaml
open Core_kernel.Std
open Bap.Std
open Graphlib.Std
open Format
include Self()
```

After you saved the file with `C-x C-s`, the `(No errors)` message
should appear in the mini-buffer. If it's not true, then make sure
that you have set up Merlin and didn't make any errors in your code.


### Defining the Command Line Interface

We will create a `Cmdline` module with the defintion of our command line
interface. It is not required to put the code in a separate
module, but it looks cleaner and makes it easier for a reader to
identify that this particular section of code deals with the command
line interface

```ocaml
let main src dst proj = ()

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
```

The code above will specify that our plugin has two command line parameters,
one is named `src` and another `dst`, both having type
`string`. It will also register the `main` function as a pass in the
analysis framework. The following stanza probably needs some
explanations:

```ocaml
  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' (main !!src !!dst))
```

The `when_ready` function takes one argument, that is a function that
will be called as soon as system configuration is processed and
command line arguments are parsed. The function will take a record,
that has only one field `get`, that is a function on itself, that will
take a value of type `'a param` and will extract a value of type '`a`
from it. The `{get=(!!)}` syntax, binds the `get` function to the
`(!!)` unary operator that can be used nicely to extract values from
parameters.

To summarize, a user specifies the command line interface, but using
the `param` function. Then the `Config.when_ready` function is used to
get the `get` function, that is a key that will unlock the parameters,
and extract the values, that are written there by the command-line
parser. The interface is described thoroughly in the reference
[documentation][3].


[3]: http://binaryanalysisplatform.github.io/bap/api/master/Bap.Std.Self.Config.html

### Building, Installing, and Running

The following three commands will build, install, and run our
analysis:

```
bapbuild check_path.plugin
bapbundle install check_path.plugin
bap ./exe --check-path-src=malloc --check-path-dst=free --pass=check-path
```

The `bapbuild check_path.plugin` command will compile the `check_path.plugin`
from the `check_path.ml`. The `bapbundle install check_path.plugin`
command will install the plugin into the place, where BAP will
automatically load (but not run) it.

The last command will run `bap` on a binary and instruct it to process
the binary with a pass named `check-path`. By default, a pass name has
the same name as the plugin name, except that all underscores are
substituted with dashes.

The `--check-path-src=malloc` will pass `malloc` as an argument to the
`src` parameter. Note, that in order to pass an argument to a plugin
parameter you need to prefix the parameter with the plugin name.

When developing, it is convenient to run all three commands at once,
with one keystroke. Fortunately, Emacs allows us to do this. To
compile for the first time, type

```
M-x compile <RET> bapbuild check_path.plugin && bapbundle install check_path.plugin && bap ./exe --check-path-src=malloc --check-path-dst=free --pass=check-path
```

This will run all three commands. You can also create a Makefile, or
store this command in some build script.

Whenever you need to recompile, just hit `C-c C-c` and Emacs will
recompile using the last compilation command.

See the [Emacs manual][4] for more information about compilation.


[4]: https://www.gnu.org/software/emacs/manual/html_node/emacs/Compilation.html#Compilation


### Trivial Proof

We will first check the trivial proof, i.e., when one of the functions
or both are not present. For that we will write a function, that will
translate a name of a function, as specified by a user, to the term
identifier of this function.

```ocaml
let find_sub prog name =
  Term.enum sub_t prog |>
  Seq.find_map ~f:(fun s ->
      Option.some_if (Sub.name s = name) (Term.tid s))
```

Now we can extend the `main` function:

```ocaml
let main src dst proj =
  let prog = Project.program proj in
  match Option.both (find_sub prog src) (find_sub prog dst) with
  | None -> printf "satisfied (trivially)\n"
  | Some (src,dst) -> printf "not implemented\n"
```

### The Skeleton Of Our Proof

We will now start writing a `verify` function, that will try to prove
that the relation doesn't hold by providing a concrete
counter-example. The `verify` function will take the program in the
Intermediate Representation (IR) and two term identifiers, one for the source function
and another for the destination function.

The function will try to find a path in the program call graph, that leads from
the source function to the destination function. If there is no such
path then for each control flow graph we will try to find a path
between a callsite that reaches the source function and a
callsite that reaches the destination function.

We will work with two different graph representations, one for the
call graph, and another for the control flow graph, let's introduce
the following abbreviations:

```ocaml
module CG = Graphs.Callgraph
module CFG = Graphs.Tid
```

Our `verify` function return type will be `proof option`, i.e., it
will return `Some proof` if the proof was found, otherwise an absence of
a proof is the proof that the relation will hold, unless there is a not yet
discovered indirect call.

Let's define the `proof` type as a variant type with two branches that
correspond to the two cases in our proof strategy:

```ocaml
type proof =
  | Calls of CG.edge path
  | Sites of CFG.edge path
```

We will use the `path` data structure from the Graphlib library, as a
particular representation of the proof term. Since we would like to output
these paths, we will start with the implementation of two pretty-printing functions for both
variants. Since they share the same polymorphic data
structure, we will first write a polymorphic function that will print
all types of paths, and then we will specialize this function to our
two concrete types:

```ocaml
let pp_path get_src get_dst ppf path =
  let print_node n = fprintf ppf "%s" (Tid.name n) in
  print_node (get_src (Path.start path));
  Seq.iter (Path.edges path) ~f:(fun e ->
      pp_print_string ppf " -> ";
      print_node (get_dst e))

let pp_calls = pp_path CG.Edge.src CG.Edge.dst
let pp_sites = pp_path CFG.Edge.src CFG.Edge.dst
```

The `pp_path` function is parametrized with the `get_src` and
`get_dst` functions that will extract, correspondingly, the source node and
the destination node of an edge. Then it will print the source of the first
edge, and iterate over all all edges and print their
destinations. Recall, that an edge consists of two endpoints and a
label (we will ignore the label for now). Thus a path is a
sequence of `m` edges, connecting `m+1` nodes, e.g.,

    (s, n0); (n0, n1); ...; (sm, d)
      /\       /\              /\
      ||       ||              ||
      e0       e1              em

Since, we want our output to be concise, we will print only `m+1`
nodes, i.e., in our case `s,n0,n1,...,d`.


Now, let's update the `main` function:

```ocaml
let main src dst proj =
  let prog = Project.program proj in
  match Option.both (find_sub prog src) (find_sub prog dst) with
  | None -> printf "satisfied (trivially)@\n"
  | Some (src,dst) -> match verify src dst prog with
    | None -> printf "satisfied (no counter-example was found)@\n"
    | Some p ->
      printf "unsatisfied by ";
      match p with
      | Calls p -> printf "calls via %a@\n" pp_calls p
      | Sites p -> printf "callsites via %a@\n" pp_sites p
```

We will also provide a stub for the `verify` function, so that we can
compile and run our program (and keep Merlin happy):

```ocaml
let verify src dst prog : proof option = None
```


### Implementing `verify`

First of all, let's try to prove, that there is a path in the program
call graph from the source function to the destination function. It
would be even easier then the trivial proof:

```ocaml
let verify src dst prog : proof option =
  let cg = Program.to_graph prog in
  match Graphlib.shortest_path (module CG) cg src dst with
  | Some path -> Some (Calls path)
  | None -> None
```

Proving that for all control flow graphs there is no such callsite to
the destination function that is reachable from a callsite to the source,
would be a little bit harder. We need to enumerate all subroutines,
obtain their control flow graphs, and then check the connectivity of each pair of
calls, that lead to the destination and source function respectively.

We will address this problems using the bottom-up approach. We will
start with the supporting code, that will enumerate all interesting
callsites from a subroutine term. For that we need to identify whether
a callsite, that is a call term, may lead to an invocation of a target
function. That would be the `reaches` predicate:

```ocaml
let reaches cg callee target =
  Graphlib.is_reachable (module CG) cg callee target
```

Now we are ready to write the `callsites` function, that will take the
call graph `cg`, the `target` function, and the subroutine term `sub`,
and return a sequence of calls that has a destination function, that
reaches `target` in the call graph.

```ocaml
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
```

In our implementation, we are ignoring local jumps, as well as return
statements and CPU interrupts. We also ignore indirect jumps and
calls, expecting that it is the task for another analysis to make all
possible control flow explicit in the graph.

Now we have all the necessary tools to finish our analysis, we will
update the `verify` function:

```ocaml
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
```

That's it, for each subroutine in the program, we generate the control
flow graph, then we iterate over all callsites that reach the source
function, and over all callsites that reach the destination function,
and check that if these two callsites are not equal, then there should
not be a path between them, and if there is, then it is the proof of
the policy violation. We added the equality test, because if the same
callsite (and we denote a callsite by the basic block that hosts the
call) reaches both the destination and the source, then it means that
we have two distinct calls in the basic block that are mutually
exclusive by the invariant of a control flow graph, or that we have
one call where the destination function is invoked strictly before the
source function. The only other case, is ruled out by the first phase
of our analysis, that proved that there is no path between the source
function and the destination function in the call graph.


## Python Implementation

The Python implementation will follow closely the OCaml
implementation, so it is recommended to read the latter, to get some
insights. The main difference is that in Python we need to build
graphs manually. It is quite possible, that we will introduce the code
for graph building in our next release of Python bindings, but so far
(as of version 1.3) we need to build them manually. Anyway, building a
graph is an excellent showcase of how to work with the complex IR
structures. But we will start from the easy stuff first.

### Running bap from Python

Unfortunately, currently we do not provide an interface for writing
real plugins in Python and so far, the only way to use BAP from Python
is to run the `bap` executable, and to parse its output. Fortunately,
we provide some supporting code for this, so running `bap` is as easy
as:

    import bap
    proj = bap.run('./echo')


We recommend to run bap in some interactive REPL, such as IPython,
that makes it easy to explore the data structures that are returned
from the bap module functions.


### Setting up the user interface

We will use the standard `argparse` module for argument parsing, and
the Networkx library to work with graphs. So let's start with writing
some boilerplate code:

```python
import bap
import networkx as nx
import argparse

def verify(prog, src_name, dst_name):
    pass

description = """
Verifies the safety property that the DST function is never called
after the SRC function is called
"""

def main():
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('filename', help='target filename')
    parser.add_argument('-s', '--src', required=True, help='the source function')
    parser.add_argument('-d', '--dst', required=True, help='the sink function')
    args = parser.parse_args()
    proj = bap.run(args.filename)
    result = verify(proj.program, args.src, args.dst)
    if result:
        print('unsatisfied ({} are reachable via {})'.format(str(result[0]), str(result[1])))
    else:
        print('satisfied')

if __name__ == '__main__':
    main()
```

We specify one positional argument for the target binary, as well as
two mandatory arguments, the names of the source and destination
functions. Our verification function, is expected to return `None`, if
no counter-example was found, or a tuple if we found a proof. The
first element of the tuple represents the kind of the proof, i.e.,
whether we found a relation in a call graph or in a control flow
graph, and the second element is the path itself.


### Building Graphs

BAP represents graphs using [Algebraic Data Types][5]. It is easier
to work with ADT using the Visitor pattern. The idea is simple. A
complex ADT, like the IR in our case, is a tree with many different
kinds of branches and leaves. The base visitor class will traverse the
tree, and every time an element of type `Xxx` is entered, a method
named `enter_Xxx` will be called (if it exists). For example, when a
basic block is entered, the `enter_Blk` method will be invoked with
the particular instance of the block.

We will implent `GraphsBuilder` that will descent
through the program IR and build two kinds of graphs simultaneously -
the program callgraph, and a list of control flow graphs (for each
subroutine). Our builder state (other than graphs itself) will include
the current subroutine and the current basic block:

```python
class GraphsBuilder(bap.adt.Visitor):
    def __init__(self):
        self.callgraph = nx.DiGraph()
        self.cfgs = []
        self.sub = None
        self.blk = None
```

Every time we enter into a new subroutine term we create an empty
digraph and append it to the list of control flow graphs. We also add
a node to the call graph and label this node with the
reference to the newly created control flow graph - this will make it
easier for us to get the CFG of a function, the functionality that we
will need later. We also update the currently processed subroutine
(we do not really store the subroutine number, as we only interested
in the term identifier of the subroutine).

```python
    def enter_Sub(self, sub):
        cfg = nx.DiGraph()
        self.callgraph.add_node(sub.id.number, name=sub.name, sub=sub, cfg=cfg)
        self.sub = sub.id.number
        self.cfgs.append(cfg)
```

When we enter a basic block, we push its term identifier as a node to
the currently built control flow graph and update the current block
number:

```python
    def enter_Blk(self, blk):
        self.cfgs[-1].add_node(blk.id.number, blk=blk)
        self.blk = blk.id.number
```

When we see a call we need to add an edge to the call graph and an edge
to the current control flow graph to represent the fallthrough edge
(if the call is not marked as a non-return call).

```python
    def enter_Call(self, jmp):
        callee = direct(jmp.target[0])
        if callee:

        fall = direct(jmp.target[1]) if len(jmp.target) == 2 else None
        if fall:
            self.cfgs[-1].add_edge(self.blk, fall.number, jmp=jmp)
```

Note, that we are ignoring indirect calls, and using the following
helper function to extract the destination of a direct jump:

```python
def direct(jmp):
    return jmp.arg if jmp is not None and jmp.constr == 'Direct' else None
```

Whenever we enter the `Goto` statement, that represent a transfer of
the control flow between two basic block in a function, we just add a
new edge, if this transfer is explicit (i.e., direct)

```python
    def enter_Goto(self, jmp):
        dst = direct(jmp.target)
        if dst:
            self.cfgs[-1].add_edge(self.blk, dst.number, jmp=jmp)
```

Finally, when a CPU exception occurs, we just add a fallthrough edge
to the currently built control flow graph

```python
    def enter_Exn(self, exn):
        fall = exn.target[1]
        if fall:
            self.cfgs[-1].add_edge(self.blk, fall.number, exn=exn)
```

[5]: http://pythonhosted.org/bap/toc-bap.adt-module.html


### Implementing the Callsites Collector

As in the OCaml version, we will collect all callsites that reach
targets in which we are interested. The implementation is rather
straight-forward, whenever we see a call, we look at the call
destination, and if it is known and reaches either the source
function, or the destination function, we add it to the corresponding
list.

```python
class CallsitesCollector(bap.adt.Visitor):
    def __init__(self, callgraph, src, dst):
        self.callgraph = callgraph
        self.caller = None
        self.src = src
        self.dst = dst
        self.srcs = []
        self.dsts = []

    def clear(self):
        self.srcs = []
        self.dsts = []

    def enter_Blk(self, blk):
        self.caller = blk.id.number

    def enter_Call(self,jmp):
        callee = direct(jmp.target[0])
        if callee:
            if nx.has_path(self.callgraph, callee.number, self.src):
                self.srcs.append(self.caller)
            if nx.has_path(self.callgraph, callee.number, self.dst):
                self.dsts.append(self.caller)
```

We also added the `clear` method that will drop both lists, as we are
planning to reuse the same collector for all subroutines.


### Implementing The Verification Procedure

Now we have a full arsenal of tools to implement the verification
procedure. It is rather straightforward, we will start by finding
target functions, using the [find][6] method that is provided by all
instances of the `Seq` class. If one of the targets is not present,
then the verification condition is satisfied trivially and we bail out
of the function. Otherwise, we instantiate `GraphsBuilder` and run it
to build the graphs. We then look at the call graph to see if there
is a path between the source and destination functions. If there is no
such path, then we are looking at each CFG for a pair of
callsites to the target functions that has a path. And if there is one,
then it is returned.

```python
def verify(prog, src_name, dst_name):
    src = prog.subs.find(src_name)
    dst = prog.subs.find(dst_name)
    if src is None or dst is None:
        return None

    graphs = GraphsBuilder()
    graphs.run(prog)
    cg = graphs.callgraph

    if nx.has_path(cg, src.id.number, dst.id.number):
        return ('calls', nx.shortest_path(cg, src.id.number, dst.id.number))

    calls = CallsitesCollector(graphs.callgraph, src.id.number, dst.id.number)

    for sub in prog.subs:
        calls.run(sub)
        cfg = graphs.callgraph.nodes[sub.id.number]['cfg']
        for src in calls.srcs:
            for dst in calls.dsts:
                if src != dst and nx.has_path(cfg, src, dst):
                    return ('sites', nx.shortest_path(cfg, src, dst))
        calls.clear()

    return None
```

[6]: http://pythonhosted.org/bap/bap.adt.Seq-class.html#find
