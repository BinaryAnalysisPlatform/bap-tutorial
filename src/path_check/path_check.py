import bap
import networkx as nx
import argparse

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



class GraphsBuilder(bap.adt.Visitor):
    def __init__(self):
        self.callgraph = nx.DiGraph()
        self.cfgs = []
        self.sub = None
        self.blk = None

    def enter_Sub(self, sub):
        cfg = nx.DiGraph()
        self.callgraph.add_node(sub.id.number, name=sub.name, sub=sub, cfg=cfg)
        self.sub = sub.id.number
        self.cfgs.append(cfg)

    def enter_Blk(self, blk):
        self.cfgs[-1].add_node(blk.id.number, blk=blk)
        self.blk = blk.id.number

    def enter_Call(self, jmp):
        callee = direct(jmp.target[0])
        if callee:
            self.callgraph.add_edge(self.sub, callee.number, jmp=jmp)

        fall = direct(jmp.target[1]) if len(jmp.target) == 2 else None
        if fall:
            self.cfgs[-1].add_edge(self.blk, fall.number, jmp=jmp)

    def enter_Goto(self, jmp):
        dst = direct(jmp.target)
        if dst:
            self.cfgs[-1].add_edge(self.blk, dst.number, jmp=jmp)

    def enter_Exn(self, exn):
        fall = exn.target[1]
        if fall:
            self.cfgs[-1].add_edge(self.blk, fall.number, exn=exn)

def direct(jmp):
    return jmp.arg if jmp is not None and jmp.constr == 'Direct' else None


def test(src, dst):
    proj = bap.run('../echo')
    return verify(proj.program, src, dst)

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
