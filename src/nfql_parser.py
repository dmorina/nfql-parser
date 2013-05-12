__author__ = 'd'
from nfql_tokenizer import *
import ply.yacc as yacc
import ipaddress
import re
import json
import types
import itertools
from sys import argv
class FilterRule:
    def __init__(self, name, value, datatype, delta, op):
        self.offset = {
            'name': name,
            'value': value,
            'datatype': datatype
        }

        self.delta = delta
        self.op = op
class GroupFilterRule:
    def __init__(self, name, value, datatype, delta, op):
        self.offset = {
            'name': name,
            'value': value,
            'datatype': datatype
        }

        self.delta = delta
        self.op = op
class Grouper(object):
    def __init__(self, name, line, modules, aggr, branches=None):
        self.name = name
        self.aggr = aggr
        self.modules = modules
        self.line = line
        self.branches = branches if branches else set()

class Filter(object):
    def __init__(self, id, line, br_mask):
        self.id = id
        self.line = line
        self.br_mask = br_mask
class Merger(object):
    def __init__(self, id, line, br_mask):
        self.id = id
        self.line = line
        self.br_mask = br_mask
class GroupFilter(object):
    def __init__(self, id, line, br_mask):
        self.id = id
        self.line = line
        self.br_mask = br_mask
class Branch(object):
    def __init__(self, id, line, filters,groupers,groupfilters):
        self.id = id
        self.line = line
        self.filters = filters
        self.groupers = groupers
        self.groupfilters = groupfilters

class Rule(object):
    def __init__(self, branch_mask, operation, args):
        self.operation = operation
        self.args = args
        self.branch_mask = branch_mask
class AggregationRule(object):
    def __init__(self, field, operation, datatype):
        self.op = operation
        self.offset= {
            'datatype':datatype,
            'name':field
        }

class GrouperRule(object):
    def __init__(self, name1, datatype1,name2,datatype2,deltavalue, op,optype):
        self.offset = {
            'f1_name': name1,
            'f1_datatype': datatype1,
            'f2_name': name2,
            'f2_datatype':datatype2
        }

        self.delta = deltavalue
        self.op = {#TODO type
            'type':optype,
            'name':op
        }
class MergerRule(object):
    def __init__(self, branch1_id,branch2_id,name1, datatype1,name2,datatype2,deltavalue, op,optype):
        self.branch1_id = branch1_id
        self.branch2_id = branch2_id
        self.offset = {
            'f1_name': name1,
            'f1_datatype': datatype1,
            'f2_name': name2,
            'f2_datatype':datatype2
        }

        self.delta = deltavalue
        self.op = {
            'type':optype,
            'name':op
        }
datatype_mappings = {'unsigned64': 'RULE_S1_64', 'unsigned32': 'RULE_S1_32', 'unsigned16': 'RULE_S1_16',
                     'unsigned8': 'RULE_S1_8','EQ':'RULE_EQ','GT':'RULE_GT','LT':'RULE_LT','LTEQ':'RULE_LE',
                     'GTEQ':'RULE_GE','IN':'RULE_IN','SUM':'RULE_SUM','COUNT':'RULE_COUNT','STATIC':'RULE_STATIC',
                     'ABS':'RULE_ABS','REL':'RULE_REL','PROD':'RULE_PROD','STDDEV':'RULE_STDDEV','BITOR':'RULE_OR',
                     'BITAND':'RULE_AND',
                     'MIN':'RULE_MIN','MAX':'RULE_MAX','UNION':'RULE_UNION','MEDIAN':'RULE_MEDIAN','MEAN':'RULE_MEAN',
                     'ipv4Address': 'RULE_S1_32', 'ipv6Address': 'RULE_S1_128', 'macAddress': 'RULE_S1_48', }
protocol_numbers = ['HOPOPT','ICMP','IGMP','GGP','IPv4','ST','TCP','CBT','EGP','IGP','BBN-RCC-MON',
                    'NVP-II','PUP','ARGUS','EMCON','XNET','CHAOS','UDP','MUX','DCN-MEAS','HMP','PRM'
                    ,'XNS-IDP','TRUNK-1','TRUNK-2','LEAF-1','LEAF-2','RDP','IRTP','ISO-TP4','NETBLT','MFE-NSP','MERIT-INP','DCCP','3PC','IDPR','XTP','DDP','IDPR-CMTP','TP++','IL',
                    'IPv6','SDRP','IPv6-Route','IPv6-Frag','IDRP','RSVP','GRE','DSR','BNA','ESP','AH','I-NLSP','SWIPE','NARP',
                    'MOBILE','TLSP','SKIP','IPv6-ICMP','IPv6-NoNxt','IPv6-Opts','CFTP','SAT-EXPAK','KRYPTOLAN','RVD','IPPC','SAT-MON','VISA','IPCV','CPNX',
                    'CPHB','WSN','PVP','BR-SAT-MON','SUN-ND','WB-MON','WB-EXPAK','ISO-IP','VMTP','SECURE-VMTP','VINES','TTP','IPTM','NSFNET-IGP','DGP','TCF','EIGRP','OSPFIGP',
                    'Sprite-RPC','LARP','MTP','AX.25','IPIP','MICP','SCC-SP','ETHERIP','ENCAP','GMTP','IFMP','PNNI','PIM','ARIS',
                    'SCPS','QNX','A/N','IPComp','SNP','Compaq-Peer','IPX-in-IP','VRRP','PGM','L2TP','DDX','IATP','STP','SRP',
                    'UTI','SMP','SM','PTP','ISIS over IPv4','FIRE','CRTP','CRUDP','SSCOPMCE','IPLT','SPS','PIPE','SCTP','FC',
                    'RSVP-E2E-IGNORE','Mobility Header','UDPLite','MPLS-in-IP','manet','HIP','Shim6','WESP','ROHC']

protocol_numbers_mappings = {'HOPOPT': 0, 'ICMP': 1, 'IGMP': 2, 'GGP': 3, 'IPv4': 4, 'ST': 5, 'TCP': 6, 'CBT': 7, 'EGP': 8, 'IGP':9,'BBN-RCC-MON':10,'NVP-II':11,'PUP':12,'ARGUS':13,'EMCON':14,'XNET':15,
       'CHAOS':16,'UDP':17,'MUX':18,'DCN-MEAS':19,'HMP':20,'PRM':21,'XNS-IDP':22,'TRUNK-1':23,'TRUNK-2':24, 'LEAF-1':25, 'LEAF-2':26, 'RDP':27, 'IRTP':28, 'ISO-TP4':29, 'NETBLT':30,
       'MFE-NSP':31, 'MERIT-INP':32, 'DCCP':33, '3PC':34, 'IDPR':35, 'XTP':36, 'DDP':37, 'IDPR-CMTP':38,
       'TP++':39,'IL':40,'IPv6':41,'SDRP':42,'IPv6-Route':43,'IPv6-Frag':44, 'IDRP':45, 'RSVP':46,
       'GRE':47, 'DSR':48, 'BNA':49, 'ESP':50, 'AH':51, 'I-NLSP':52, 'SWIPE':53,'NARP':54,'MOBILE':55,
       'TLSP':56,'SKIP':57,'IPv6-ICMP':58,'IPv6-NoNxt':59,
       'IPv6-Opts':60, 'CFTP':61, 'SAT-EXPAK':62, 'KRYPTOLAN':63, 'RVD':64, 'IPPC':65, 'SAT-MON':66,
       'VISA':67,'IPCV':68,'CPNX':69,'CPHB':70,'WSN':71,'PVP':72,'BR-SAT-MON':73,
       'SUN-ND':74, 'WB-MON':75, 'WB-EXPAK':76, 'ISO-IP':77, 'VMTP':78, 'SECURE-VMTP':79, 'VINES':80,
       'TTP':81, 'IPTM':82, 'NSFNET-IGP':83, 'DGP':84, 'TCF':84, 'EIGRP':85, 'OSPFIGP':86,
       'Sprite-RPC':87,'LARP':88,'MTP':89,'AX.25':90,'IPIP':91,'MICP':92,'SCC-SP':93,'ETHERIP':94,
       'ENCAP':95,'GMTP':96,'IFMP':97,'PNNI':98,'PIM':99,'ARIS':100, 'SCPS':101, 'QNX':102, 'A/N':103,
       'IPComp':104, 'SNP':105, 'Compaq-Peer':106, 'IPX-in-IP':107,'VRRP':108,'PGM':109,'L2TP':110,
       'DDX':111,'IATP':112,'STP':113,'SRP':114, 'UTI':115, 'SMP':116, 'SM':117, 'PTP':118,
       'ISIS over IPv4':119, 'FIRE':120, 'CRTP':121, 'CRUDP':122, 'SSCOPMCE':123, 'IPLT':124,
       'SPS':125, 'PIPE':126, 'SCTP':127, 'FC':128, 'RSVP-E2E-IGNORE':129, 'Mobility Header':130,
       'UDPLite':131, 'MPLS-in-IP':132, 'manet':133,'HIP':134,'Shim6':135,'WESP':136,'ROHC':137
}


class Parser :
    tokens=[]
    tokens = Tokenizer.tokens
    filters = []
    branch_id_mapping={}
    br_id = 0
    groupers=[]
    grouper= Grouper('',0,'','','')
    groupfilters=[]
    branches=[]
    branch_ids=[]
    merger=[]
    ungrouper=[]
    filterRules=[]
    xml=[]
    entities={}
    def p_stage(self,p):
        '''
            stage : branches merger ungrouper

        '''
        p[0]=[]
    def p_branches(self,p):
        '''
        branches : branch newline branches
        '''
        p[0]=p[1]
    def p_branches_empty(self,p):
        'branches :'
        p[0]=[]
    def p_branch(self,p):
        '''
        branch : branchKeyword id '{' pipeline_stage_1n '}'

                | branchKeyword id '{' newline pipeline_stage_1n '}'
                | branchKeyword id '{' pipeline_stage_1n newline '}'
                | branchKeyword id '{' newline pipeline_stage_1n newline '}'
                | branchKeyword id newline '{' pipeline_stage_1n '}' newline
                | branchKeyword id newline '{' pipeline_stage_1n newline '}'
                | branchKeyword id newline '{' newline pipeline_stage_1n newline '}'
                | branchKeyword id newline '{' newline pipeline_stage_1n '}'

        '''
        p[0]= Branch(p[2],p.lineno(2),self.filters,self.groupers,self.groupfilters)
        if p[2] in self.branch_id_mapping.keys():
            print("Branch ID '%s' already used, line %s"%(p[2],p.lineno(2)))
            exit(-1)
        self.branches.append(p[0])
        self.branch_ids.append(p[2])
        self.branch_id_mapping[p[2]]=self.br_id
        self.br_id = self.br_id + 1
        self.groupfilters=[]
        self.filters=[]
        self.groupers=[]

    def p_branch_empty(self, p):
        'branch :'
        p[0]=[]
    def p_pipeline_stage_1n(self,p):
        """pipeline_stage_1n : pipeline_stage newline pipeline_stage_1n
                                | newline pipeline_stage newline pipeline_stage_1n newline
        """
        # add a name mapping:
        p[0]=p[1]

    def p_pipeline_stage_end(self,p):
        'pipeline_stage_1n :'

    def p_pipeline_stage(self,p):
        '''
        pipeline_stage : filter
                        | grouper
                        | groupfilter
        '''

        p[0] = p[1]
    def p_filter(self,p):
        '''
        filter : filterKeyword id '{' filter_rule_1n '}'
        '''
        p[0] = Filter(p[2], p.lineno(2), p[4])
        self.filters.append(p[0])

    def p_filter_newline(self, p):
        '''
        filter : filterKeyword id newline '{' filter_rule_1n '}'
        '''
        p[0] = Filter(p[2], p.lineno(2), p[5])
        self.filters.append(p[0])
    def p_filter_rule_1n(self, p):
        'filter_rule_1n : filter_rule newline filter_rule_1n'
        p[3].extend([p[1]])
        p[0] = p[3]

    def p_filter_rule_1n_newline(self, p):
        'filter_rule_1n : newline filter_rule newline filter_rule_1n'
        p[4].extend([p[2]])
        p[0] = p[4]

    def p_filter_rule_0(self,t):
        'filter_rule_1n :'
        t[0] = []

    def p_filter_rule(self,t):
        '''
        filter_rule : or_rule
        '''
        t[0] = t[1]

    def p_or_rule(self,p):
        '''
        or_rule : rule_or_not opt_rule
        '''
        if len(p[2]) > 0:
            ors = [p[1]]
            ors.extend(p[2])
            p[0] = ors
        else:
            p[0] = [p[1]]


    def p_term_opt_rule(self,t):
        'opt_rule :'
        t[0] = []

    def p_opt_rule(self,t):
        '''opt_rule : ORKeyword rule_or_not opt_rule'''
        r = [t[2]]
        r.extend(t[3])
        t[0] = r


    def p_rule_or_not(self,p):
        '''
        rule_or_not : rule  
        '''
        p[0] = p[1]

    def p_rule(self,t):
        '''
        rule : infix_rule
        '''
        t[0] = t[1]
    def p_delta_rule(self,p):
        'infix_rule : arg_names op arg deltaKeyword delta_arg'
        dt = p[1][0]
        opt = p[2]
        value = p[3][0]
        notval = False
        if (dt == 'protocolIdentifier'):
            try:
                if (p[3][0] in protocol_numbers_mappings.items()):
                    pass
            except:
                notval = True
            if notval:
                try:
                    value = protocol_numbers_mappings[p[3][0]]
                except KeyError:
                    print("Invalid protocol name/value '%s', line %s" % (p[3][0], p.lineno(1)))
                    exit(-1)

        try:
            if (self.entities[dt] == 'unsigned8'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 8):
                    pass
                else:
                    print('Value out of range line %s: 8bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned16'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 16):
                    pass
                else:
                    print('Value out of range line %s: 16bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned32'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 32):
                    pass
                else:
                    print('Value out of range line %s: 32bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned64'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 64):
                    pass
                else:
                    print('Value out of range line %s: 64bit' % p.lineno(1))
                    exit(-1)
        except:
            pass
        try:
            rdt = datatype_mappings[self.entities[dt]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))

        operator = datatype_mappings[opt]

        fl = FilterRule(dt, p[3][0], rdt, p[5], operator)
        self.filterRules.append(fl)
        p[1].extend(p[3])
        p[0] = fl
    def p_infix_rule(self,p):
        'infix_rule : arg_names op arg'
        dt=p[1][0]
        opt=p[2]
        value=p[3][0]
        notval=False
        if(dt=='protocolIdentifier'):
            try:
                if(p[3][0] in protocol_numbers_mappings.items()):
                    pass
            except:
                notval=True
            if notval:
                try:
                    value=protocol_numbers_mappings[p[3][0]]
                except KeyError:
                    print("Invalid protocol name/value '%s', line %s"%(p[3][0],p.lineno(1)))
                    exit(-1)

        try:
            if (self.entities[dt] == 'unsigned8'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 8):
                    pass
                else:
                    print('Value out of range line %s: 8bit' % p.lineno(1))
                    exit(-1)
            elif(self.entities[dt] == 'unsigned16'):
                if(len('{0:08b}'.format(int(p[3][0])))<=16):
                    pass
                else:
                    print('Value out of range line %s: 16bit'%p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned32'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 32):
                    pass
                else:
                    print('Value out of range line %s: 32bit' % p.lineno(1))
                    exit(-1)
            elif(self.entities[dt] == 'unsigned64'):
                if(len('{0:08b}'.format(int(p[3][0])))<=64):
                    pass
                else:
                    print('Value out of range line %s: 64bit'%p.lineno(1))
                    exit(-1)
        except:
            pass
        try:
            rdt=datatype_mappings[self.entities[dt]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
        try:
            operator=datatype_mappings[str(opt).upper()]
        except KeyError:
            print("Invalid operator '%s', line %s"%(opt,p.lineno(1)))
            exit(-1)
        fl=FilterRule(dt,value,rdt,0,operator)
        #self.filterRules.append(fl)
        #p[1].extend(p[3])
        p[0]=fl

    def p_op(self,p):
        '''
        op : EQ
           | LT
           | GT
           | LTEQ
           | GTEQ
           | ML
           | MG
           | inKeyword
           | notinKeyword
        '''
        p[0] = p[1] #lineno


    def p_args(self,p):#TODO
       '''
       args : '(' args_n ')'
       '''
       p[0] = p[2]

    def p_args_n(self, p):
        '''
            args_n : arg ','  args_n
        '''
        p[0] = p[1]
        p[0].extend(p[3])

    def p_args_one(self, p):
        '''
            args_n : arg
        '''
        p[0] = p[1]

    def p_args_n_empty(self,p):
        '''
            args_n :
        '''
        p[0] = []

    def p_arg(self,p): #TODO
        '''
        arg : IPv6
            | IPv4
            | CIDR
            | MAC
            | int
            | args
        '''
        p[0] = [p[1]]

    def p_arg_names(self,p):
        '''
        arg_names : id
        '''
        p[0]=[p[1]]
    def p_cidr(self,p):
        '''
        CIDR : IPv4 '/' int
             | IPv6 '/' int
        '''
        lst=[]
        try:
            for ip in ipaddress.ip_network(str(p[1])+str(p[2])+str(p[3])):
                lst.append(str(ip))
        except:
            print("Invalid CIDR '%s', line %s"%(str(p[1])+str(p[2])+str(p[3]),p.lineno(1)))
        p[0] = lst

    ####Grouper####
    def p_grouper(self, p):
        """grouper : grouperKeyword id '{' grouper_rule1_n aggregate '}'
                    | grouperKeyword id '{' grouper_rule1_n aggregate  newline '}'
        """
        p[0] = Grouper(p[2], p.lineno(2), p[4], p[5])
        #self.grouper = p[0]
        self.groupers.append(p[0])

    def p_grouper_em(self, p):
        """grouper : grouperKeyword id '{'  '}'
                    | grouperKeyword id '{'  newline '}'
                    | grouperKeyword id newline '{' '}'
                    | grouperKeyword id newline '{' newline '}'
        """
        p[0] = Grouper(p[2],p.lineno(2),[],[])
        #self.grouper = p[0]
        self.groupers.append(p[0])

    def p_grouper_newline0(self, p):
        """grouper : grouperKeyword id newline '{' newline grouper_rule1_n aggregate '}'
                    | grouperKeyword id newline '{' newline grouper_rule1_n aggregate newline '}'
        """
        p[0] = Grouper(p[2], p.lineno(2), p[6], p[7])
        self.grouper = p[0]
        #print(p[0].modules)
        self.groupers.append(p[0])

    def p_grouper_newline(self, p):
        """grouper : grouperKeyword id newline '{' grouper_rule1_n aggregate '}'
                    | grouperKeyword id newline '{' grouper_rule1_n aggregate newline '}'
        """
        p[0] = Grouper(p[2], p.lineno(2), p[5], p[6])
        self.grouper = p[0]
        #print(p[0].modules)
        self.groupers.append(p[0])

    def p_grouper_rule1_n(self, p):
        'grouper_rule1_n : grouper_rule_n newline grouper_rule1_n'
        p[3].extend([p[1]])
        p[0] = p[3]


    def p_grouper_rule0(self, p):
        'grouper_rule1_n :'
        p[0] = []
    def p_grouper_rule_n(self,p):
        'grouper_rule_n : grouper_or_rule'
        p[0]=p[1]

    def p_grouper_or_rule(self,p):
        'grouper_or_rule : grouper_rule g_opt_rule'
        if len(p[2]) > 0:
            ors = [p[1]]
            ors.extend(p[2])
            p[0] = ors
        else:
            p[0] = [p[1]]
    def p_grouper_opt_rule_empty(self,p):
        'g_opt_rule :'
        p[0]=[]
    def p_grouper_opt_rule(self,p):
        'g_opt_rule : ORKeyword grouper_rule g_opt_rule'
        r = [p[2]]
        r.extend(p[3])
        p[0] = r
    def p_grouper_rule(self, p):#TODO
        'grouper_rule : id grouper_op id'
        try:
            rdt1=datatype_mappings[self.entities[p[1]]]
            rdt2=datatype_mappings[self.entities[p[3]]]
        except KeyError:
            print('Invalid field name, line %s'%p.lineno)
        operator = datatype_mappings[p[2]]
        if(rdt1 != rdt2):
            print('Datatype mismatch line %s'%p.lineno)
            exit(1)
        p[0] = GrouperRule(p[1],rdt1,p[3],str(rdt2).replace("S1","S2"),0,operator,'RULE_REL')


    ##absolute id=arg
    def p_grouper_rule_abs(self,p):#TODO fix the dt
        'grouper_rule : id grouper_op g_arg'
        dt = p[1]
        try:
            rdt1 = datatype_mappings[self.entities[p[1]]]
            #rdt2 = datatype_mappings[self.entities[p[3]]]
        except KeyError:
            print("Invalid field name '%s', line %s" % (str(p[1]),p.lineno(2)))
            exit(-1)
        try:
            if (self.entities[dt] == 'unsigned8'):
                if (len('{0:08b}'.format(int(p[3]))) <= 8):
                    pass
                else:
                    print('Value out of range line %s: 8bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned16'):
                if (len('{0:08b}'.format(int(p[3]))) <= 16):
                    pass
                else:
                    print('Value out of range line %s: 16bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned32'):
                if (len('{0:08b}'.format(int(p[3]))) <= 32):
                    pass
                else:
                    print('Value out of range line %s: 32bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned64'):
                if (len('{0:08b}'.format(int(p[3]))) <= 64):
                    pass
                else:
                    print('Value out of range line %s: 64bit' % p.lineno(1))
                    exit(-1)
        except :
            pass

        operator = datatype_mappings[p[2]]
        p[0] = GrouperRule(p[1], rdt1, p[3], str(rdt1).replace("S1","S2"), 0, operator, 'RULE_ABS')

    def p_grouper_arg(self, p):
        '''
        g_arg : IPv6
            | IPv4
            | CIDR
            | MAC
            | int

        '''
        p[0] = p[1]
    def p_grouper_rule_delta(self, p):
        '''
        grouper_rule : id grouper_op id deltaKeyword delta_arg
        '''
        try:
            rdt1 = datatype_mappings[self.entities[p[1]]]
            rdt2 = datatype_mappings[self.entities[p[3]]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
            exit(-1)
        operator = datatype_mappings[p[2]]
        if (rdt1 != rdt2):
            print('Datatype mismatch line %s' % p.lineno(2))
            exit(-1)
        p[0] = GrouperRule(p[1],rdt1,p[3],str(rdt2).replace("S1","S2"),p[5],operator,'RULE_REL')


    def p_grouper_op(self, p):
        '''
        grouper_op : EQ
                    | LT
                    | GT
                    | GTEQ
                    | LTEQ
        '''
        p[0] = p[1]

    def p_delta_arg(self, p):
        '''
        delta_arg :     time
                    | int
        '''
        p[0] = p[1]

    def p_time(self, p):
        '''
        time :  int sKeyword
                | int msKeyword
                | int minKeyword
        '''
        # the number should be in ms:
        if p[2] == 's':
            p[1].value = p[1].value * 1000
        if p[2] == 'min':
            p[1].value = p[1].value * 60 * 1000
        p[0] = p[1]

    def p_aggregate_empty(self,p):
        'aggregate :'
        p[0]=[]
    def p_aggregate(self, p):
        "aggregate : aggregateKeyword '{' aggr1_n '}'"
        p[0] = p[3]

    def p_aggregate_new(self, p):
        "aggregate : newline aggregateKeyword '{' aggr1_n '}'"
        p[0] = p[4]


    def p_aggregate_newline(self, p):
        "aggregate : aggregateKeyword newline '{' aggr1_n '}'"
        p[0] = p[4]

    def p_aggr1_n(self, p):
        'aggr1_n : aggr_rule newline aggr1_n'
        p[3].extend([p[1]])
        p[0] = p[3]

    def p_aggr1_n_newline(self, p):
        'aggr1_n : newline aggr_rule newline aggr1_n'
        p[4].extend([p[2]])
        p[0] = p[4]

    def p_aggr1_n_empty(self, p):
        'aggr1_n : '
        p[0]=[]

    def p_aggr_rule(self,p):
        "aggr_rule : aggr_op '(' id ')'"
        try:
            rdt1 = datatype_mappings[self.entities[p[3]]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
            exit(-1)
        try:
            op = datatype_mappings[str(p[1]).upper()]
        except:
            print('Invalid operator, line %s' % p.lineno(2))
            exit(-1)
        invalidTypes=['ipv4Address','ipv6Address ','macAddress']
        if(str(p[1].upper())=='SUM' or str(p[1].upper())=='MEAN' or str(p[1].upper())=='UNION'):
            if(str(self.entities[p[3]]) in invalidTypes):
                print('Operators SUM, MEAN and UNION are not allowed on data types ipv4Address, ipv6Address and macAddress')
                exit(-1)
        p[0]=[AggregationRule(p[3],op,rdt1)]

    def p_aggr_op(self, p):
        '''
        aggr_op : minKeyword
                | maxKeyword
                | sumKeyword
                | meanKeyword
                | staticKeyword
                | unionKeyword
                | countKeyword
                | bitANDKeyword
                | bitORKeyword
                | id
        '''
        p[0] = p[1]
### GroupFilter
    def p_groupfilter(self, p):
        '''
        groupfilter : groupfilterKeyword id '{' groupfilter_rule_1n '}'
        '''
        p[0] = GroupFilter(p[2], p.lineno(2), p[4])
        #print(p[4][0].op)
        self.groupfilters.append(p[0])

    def p_groupfilter_newline(self, p):
        '''
        groupfilter : groupfilterKeyword id newline '{' groupfilter_rule_1n '}'
        '''
        p[0] = GroupFilter(p[2], p.lineno(2), p[5])
        #print(p[0].br_mask)
        self.groupfilters.append(p[0])

    def p_groupfilter_rule_1n(self, p):
        'groupfilter_rule_1n : groupfilter_rule newline groupfilter_rule_1n'
        p[3].extend([p[1]])
        p[0] = p[3]

    def p_groupfilter_rule_1n_newline(self, p):
        'groupfilter_rule_1n : newline groupfilter_rule newline groupfilter_rule_1n'
        p[4].extend([p[2]])
        p[0] = p[4]

    def p_grouperfilter_rule_0(self, t):
        'groupfilter_rule_1n :'
        t[0] = []

    def p_groupfilter_rule(self, t):
        '''
        groupfilter_rule : gf_or_rule
        '''
        t[0] = t[1]

    def p_gf_or_rule(self, p):
        '''
        gf_or_rule : gf_rule gf_opt_rule
        '''
        if len(p[2]) > 0:
            ors = [p[1]]
            ors.extend(p[2])
            p[0] = ors
        else:
            p[0] = [p[1]]


    def p_gf_term_opt_rule(self, t):
        'gf_opt_rule :'
        t[0] = []

    def p_gf_opt_rule(self, t):
        '''gf_opt_rule : ORKeyword gf_rule gf_opt_rule'''
        r = [t[2]]
        r.extend(t[3])
        t[0] = r
    def p_gf_rule(self,p):
        'gf_rule : arg_names op arg'
        dt = p[1][0]
        opt = p[2]
        try:
            if (self.entities[dt] == 'unsigned8'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 8):
                    pass
                else:
                    print('Value out of range line %s: 8bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned16'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 16):
                    pass
                else:
                    print('Value out of range line %s: 16bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned32'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 32):
                    pass
                else:
                    print('Value out of range line %s: 32bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned64'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 64):
                    pass
                else:
                    print('Value out of range line %s: 64bit' % p.lineno(1))
                    exit(-1)
        except:
            pass
        try:
            rdt = datatype_mappings[self.entities[dt]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
            exit(-1)
        operator = datatype_mappings[opt]
        fl = GroupFilterRule(dt, p[3][0], rdt, 0, operator)
        p[0] = fl

    def p_gf_rule_delta(self, p):
        'gf_rule : arg_names op arg deltaKeyword delta_arg'
        dt = p[1][0]
        opt = p[2]
        try:
            if (self.entities[dt] == 'unsigned8'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 8):
                    pass
                else:
                    print('Value out of range line %s: 8bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned16'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 16):
                    pass
                else:
                    print('Value out of range line %s: 16bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned32'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 32):
                    pass
                else:
                    print('Value out of range line %s: 32bit' % p.lineno(1))
                    exit(-1)
            elif (self.entities[dt] == 'unsigned64'):
                if (len('{0:08b}'.format(int(p[3][0]))) <= 64):
                    pass
                else:
                    print('Value out of range line %s: 64bit' % p.lineno(1))
                    exit(-1)
        except:
            pass
        try:
            rdt = datatype_mappings[self.entities[dt]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
        operator = datatype_mappings[opt]
        fl = GroupFilterRule(dt, p[3][0], rdt, int(p[5]), operator)
        p[0] = fl
### Merger
    def p_merger_empty(self, p):
        'merger :'
        p[0]=[]
    def p_merger(self,p):
        '''
        merger : mergerKeyword '{' merger_rule_1n '}'
                | mergerKeyword '{' merger_rule_1n '}' newline
        '''
        p[0]=Merger('merger',p.lineno(2),p[3])
        self.merger.append(p[0])
    def p_merger_empty_br(self,p):
        '''
        merger : mergerKeyword '{' '}'
                | mergerKeyword '{' '}' newline
                | mergerKeyword '{' newline '}' newline
                | mergerKeyword newline '{' '}'
                | mergerKeyword newline '{' '}' newline
        '''
        p[0]=[]

    def p_merger_newline(self, p):
        '''
        merger : mergerKeyword newline '{' merger_rule_1n '}'
                | mergerKeyword newline '{' merger_rule_1n '}' newline
        '''
        p[0] = Merger('merger', p.lineno(2), p[4])
        self.merger.append(p[0])

    def p_merger_rule_1n(self, p):
        'merger_rule_1n : merger_rule newline merger_rule_1n'
        p[3].extend([p[1]])
        p[0] = p[3]

    def p_merger_rule_1n_newline(self, p):
        'merger_rule_1n : newline merger_rule newline merger_rule_1n'
        p[4].extend([p[2]])
        p[0] = p[4]

    def p_merger_rule_0(self, t):
        'merger_rule_1n :'
        t[0] = []

    def p_merger_rule(self, t):
        '''
        merger_rule : merger_or_rule
        '''
        t[0] = t[1]

    def p_merger_or_rule(self, p):
        '''
        merger_or_rule : merger_m_rule merger_opt_rule
        '''
        if len(p[2]) > 0:
            ors = [p[1]]
            ors.extend(p[2])
            p[0] = ors
        else:
            p[0] = [p[1]]


    def p_merger_term_opt_rule(self, t):
        'merger_opt_rule :'
        t[0] = []

    def p_merger_opt_rule(self, t):
        'merger_opt_rule : ORKeyword merger_m_rule merger_opt_rule'
        r = [t[2]]
        r.extend(t[3])
        t[0] = r
    def p_m_rule(self,p):
        "merger_m_rule : id '.' id allen_op id '.' id"
        if p[1] in self.branch_ids:
            pass
        else:
            print("Undefined branch id '%s' used line %s"%(p[1],p.lineno(2)))
            exit(-1)
        if p[5] in self.branch_ids:
            pass
        else:
            print("Undefined branch id '%s' used line %s" % (p[5], p.lineno(2)))
            exit(-1)

        try:
            rdt1 = datatype_mappings[self.entities[p[3]]]
            rdt2 = datatype_mappings[self.entities[p[7]]]
        except KeyError:
            print('Invalid field name, line %s' % p.lineno(2))
            exit(-1)
        operator = datatype_mappings[p[4]]
        if (rdt1 != rdt2):
            print('Datatype mismatch line %s' % p.lineno(2))
            exit(1)

        p[0]=MergerRule(self.branch_id_mapping[p[1]],self.branch_id_mapping[p[5]],p[3],rdt1,p[7],str(rdt2).replace("S1","S2"),0,operator,'RULE_REL')


    def p_allen_op(self, p):
        '''
        allen_op : LT
                | GT
                | EQ
                | mKeyword
                | miKeyword
                | oKeyword
                | oiKeyword
                | sKeyword
                | siKeyword
                | dKeyword
                | diKeyword
                | fKeyword
                | fiKeyword
                | eqKeyword
        '''
        p[0]=p[1]
### Ungrouper
    def p_ungrouper(self,p):
        'ungrouper :'
        p[0] = []

    def p_ungrouper_empty(self, p):
        '''
        ungrouper : ungrouperKeyword '{' '}'
                | ungrouperKeyword '{' '}' newline
                | ungrouperKeyword '{' newline '}' newline
                | ungrouperKeyword newline '{' '}'
                | ungrouperKeyword newline '{' '}' newline
        '''
        self.ungrouper.append('ungrouper')
        p[0] = []
    def p_error(self,p):
        print("Syntax error at input line %s"%p.lineno)

    def Parse(self, data):
        #self.Error = False  tracking=True, debug=1, parse
        # yacc debug = True
        parser = yacc.yacc(module=self)

        lexer = Tokenizer().build()
        self.xml = Tokenizer.names
        self.entities=Tokenizer.entities
        return yacc.parse(data,tracking=True,lexer=lexer)


