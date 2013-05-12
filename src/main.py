import re
import json
import types
import itertools
import sys
from nfql_parser import *

import shutil
if __name__ == "__main__":

    files = len(sys.argv)
    for i in range(files):
        exists=True
        if(i!=0):
            try:
                inp = open((sys.argv[i]))
            except IOError:
                print('Error opening file %s'%str(sys.argv[i]))
                exists=False
            if(exists):
                parsr = Parser()
                parsr.Parse(inp.read()+'\n')
                branchset = []
                query={}
                filter=[]
                mclause = []

                grouper=[]
                if(len(parsr.branches)==0):
                    print('Empty file!')
                    exit(-1)
                if(len(parsr.merger)>1):
                    print('Multiple mergers defined')
                    exit(-1)
                if (len(parsr.ungrouper) > 1):
                    print('Multiple ungroupers defined')
                    exit(-1)
                for branch in parsr.branches:
                    grules=[]
                    gclause = []

                    gf_clause = []
                    clause = []
                    aggregation={'clause':[]}
                    lst=[]

                    if(len(branch.groupers)>0 and len(branch.groupfilters)>0):
                        if (len(branch.groupers[0].modules)==0 and len(branch.groupfilters[0].br_mask)>0):
                            print('Groupfilter defined without a grouper!')
                            exit(-1)
                    if (len(branch.groupers) > 1):
                        print('Multiple groupers defined inside one branch')
                        exit(-1)
                    if (len(branch.filters) > 1):
                        print('Multiple filters defined inside one branch')
                        exit(-1)
                    if (len(branch.groupfilters) > 1):
                        print('Multiple groupfilters defined inside one branch')
                        exit(-1)
                    for gr in branch.groupers:
                        for grule in gr.modules:
                            grules.append(grule)
                        for aggr in gr.aggr:
                            for a_rule in aggr:
                                lst.append({'term': vars(a_rule)})
                        aggregation={'clause': lst}
                        lst=[]
                        for rule in list(itertools.product(*grules)):
                            for r in rule:
                                lst.append({'term': vars(r)})
                            gclause.append({'clause': lst})
                            lst = []
                    grouper = []
                    grouper = {'dnf-expr': gclause,'aggregation':aggregation}
                    for fl in branch.filters:
                        #print(fl.br_mask)
                        rules = []
                        lst = []

                        for frule in fl.br_mask:
                            #print(frule)
                            rules.append(frule)
                        for rule in list(itertools.product(*rules)):
                            for r in rule:
                                lst.append({'term': vars(r)})
                            clause.append({'clause': lst})
                            lst = []
                    filter = {'dnf-expr': clause}
                    for gf in branch.groupfilters:
                        gfrules = []
                        gflst = []

                        for gfrule in gf.br_mask:
                            gfrules.append(gfrule)
                        #print(gfrules)
                        for rule in list(itertools.product(*gfrules)):
                            for r in rule:
                                gflst.append({'term': vars(r)})
                            gf_clause.append({'clause': gflst})
                            gflst = []
                    groupfilter = []
                    groupfilter = {'dnf-expr': gf_clause}
                    branchset.append({'filter': filter,'grouper':grouper,'groupfilter':groupfilter})
                for merger in parsr.merger:
                    mrules = []
                    lst = []
                    for mrule in merger.br_mask:
                        #print(frule)
                        mrules.append(mrule)
                    for rule in list(itertools.product(*mrules)):
                        for r in rule:
                            lst.append({'term': vars(r)})
                        mclause.append({'clause': lst})
                        lst = []
                merger={'dnf-expr': mclause}
                query['merger']=merger
                query['branchset']= branchset
                if(len(parsr.ungrouper)==1):
                    query['ungrouper'] = {}

                fjson = json.dumps(query, indent=2)
                file = open('%s.json'%inp.name[:-4], 'w')
                assert file.write(fjson)
				
                file.close