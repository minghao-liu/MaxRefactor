from pysat.formula import WCNF
from pysat.pb import *

from maxsat import anytime_maxsat_solve

def get_bool_var(f, args, nvar):
    if args not in f:
        f[args] = nvar + 1
        nvar += 1
    return f[args], nvar

def get_bool_const(f, args):
   return f[args] if args in f else False

def get_atmost_encoding(l, w, b, nvar):
    cnf = PBEnc.atmost(lits=l, weights=w, bound=b, top_id=nvar)
    for c in cnf.clauses:
        for l in c:
            nvar = max(nvar, abs(l))
    return cnf.clauses, nvar

def get_new_arg(body_arg_id, pred_list):
    arg = f"X{body_arg_id}"
    while arg in pred_list:
        body_arg_id += 1
        arg = f"X{body_arg_id}"
    return arg, body_arg_id + 1

def do_compression(bk, settings):
    rule_list = []
    atom_list = set()
    pred_list = set()
    for rule in bk["rule"]:
        rule_list.append(rule)
    for atom in bk["atom"]:
        atom_list.add(atom)
        pred_list.add(bk["atom"][atom]["pred"])
    atom_list = list(atom_list)
    pred_list = list(pred_list)
    inv_rule_num = settings.inv_rule_num
    timeout = settings.timeout
    solver = "uwrmaxsat"
    solver_args = "-v0 -no-bin -m -bm"

    debug_flag = False
    if debug_flag:
        fp_log = open("debug.log", "w")

    ### auxiliary constants ###
    rule_pred = {}
    for rule in rule_list:
        for pred in pred_list:
            rule_pred[(rule, pred)] = 0
        for atoms in bk["rule"][rule]["body"]:
            rule_pred[(rule, bk["atom"][atoms]["pred"])] += 1
    max_pred = {}
    max_use = 0
    for rule, pred in rule_pred:
        if pred not in max_pred:
            max_pred[pred] = 0
        max_pred[pred] = max(max_pred[pred], rule_pred[(rule, pred)])
        max_use = max(max_use, max_pred[pred])
    atom_rule = {}
    for rule in rule_list:
        for atom in bk["rule"][rule]["body"]:
            atom_rule[atom] = rule

    ### variables ###
    nvar = 0
    inv_body_pred = {}
    rule_use_inv = {}
    covered = {}
    inv_used = {}
    is_covered = {}
    
    ### constraints ###
    f = WCNF()
    # rule_use_inv(r,inv,k) -> rule_use_inv(r,inv,k-1)
    for rule in rule_list:
        for inv in range(1, inv_rule_num+1):
            for k in range(2, max_use+1):
                var1, nvar = get_bool_var(rule_use_inv, (rule, inv, k), nvar)
                var2, nvar = get_bool_var(rule_use_inv, (rule, inv, k-1), nvar)
                f.append([-var1, var2])
                if debug_flag:
                    print(f"rule_use_inv({rule},inv{inv},{k}) : bool({var1})", file=fp_log)
                    print(f"rule_use_inv({rule},inv{inv},{k-1}) : bool({var2})", file=fp_log)
                    print(f"rule_use_inv({rule},inv{inv},{k}) -> rule_use_inv({rule},inv{inv},{k-1})", file=fp_log)
    # inv_body_pred(inv,pred,x1) -> not inv_body_pred(inv,pred,x2)
    for inv in range(1, inv_rule_num+1):
        for pred in pred_list:
            for x1 in range(1, max_pred[pred]+1):
                for x2 in range(x1+1, max_pred[pred]+1):
                    var1, nvar = get_bool_var(inv_body_pred, (inv, pred, x1), nvar)
                    var2, nvar = get_bool_var(inv_body_pred, (inv, pred, x2), nvar)
                    f.append([-var1, -var2])
                    if debug_flag:
                        print(f"inv_body_pred(inv{inv},{pred},{x1}) -> not inv_body_pred(inv{inv},{pred},{x2})", file=fp_log)
    # rule_use_inv(r,inv,k) /\ inv_body_pred(inv,pred,x) -> rule_pred(r,pred)>0
    for rule in rule_list:
        for pred in pred_list:
            if rule_pred[(rule, pred)] == 0:
                for inv in range(1, inv_rule_num+1):
                    for k in range(1, max_use+1):
                        for x in range(1, max_pred[pred]+1):
                            var1, nvar = get_bool_var(rule_use_inv, (rule, inv, k), nvar)
                            var2, nvar = get_bool_var(inv_body_pred, (inv, pred, x), nvar)
                            f.append([-var1, -var2])
                            if debug_flag:
                                print(f"not rule_use_inv({rule},inv{inv},{k}) or not inv_body_pred(inv{inv},{pred},{x})", file=fp_log)
    # inv_used(inv) <-> Exists.(r,k): rule_use_inv(r,inv,k)
    for inv in range(1, inv_rule_num+1):
        var1, nvar = get_bool_var(inv_used, inv, nvar)
        or_list = []
        or_list_str = []
        for rule in rule_list:
            for k in range(1, max_use+1):
                var2, nvar = get_bool_var(rule_use_inv, (rule, inv, k), nvar)
                f.append([var1, -var2])
                if debug_flag:
                    print(f"rule_use_inv({rule},inv{inv},{k}) -> inv_used(inv{inv})", file=fp_log)
                or_list.append(var2)
                or_list_str.append(f"rule_use_inv({rule},inv{inv},{k})")
        f.append([-var1] + or_list)
        if debug_flag:
            print(f"inv_used(inv{inv}) -> {' or '.join(or_list_str)}", file=fp_log)
    # inv1!=inv2 \/ k1!=k2 -> (covered(atom,inv1,k1) -> not covered(atom,inv2,k2))
    # for atom in atom_list:
    #     for inv1, k1 in [(i, j) for i in range(1, inv_rule_num+1) for j in range(1, max_use+1)]:
    #         for inv2, k2 in [(i, j) for i in range(1, inv_rule_num+1) for j in range(1, max_use+1)]:
    #             # if inv1 == inv2 and k1 == k2:
    #             #     continue
    #             if inv1 < inv2 or (inv1 == inv2 and k1 < k2):
    #                 var1, nvar = get_bool_var(covered, (atom, inv1, k1), nvar)
    #                 var2, nvar = get_bool_var(covered, (atom, inv2, k2), nvar)
    #                 f.append([-var1, -var2])
    #                 if debug_flag:
    #                     print(f"covered({atom},inv{inv1},{k1}) -> not covered({atom},inv{inv2},{k2})", file=fp_log)
    # covered(atom,inv,k) -> rule_use_inv(atom.r,inv,k) /\ inv_body_pred(inv,atom.pred,x)
    for atom in atom_list:
        pred = bk["atom"][atom]["pred"]
        rule = atom_rule[atom]
        for inv in range(1, inv_rule_num+1):
            for k in range(1, max_use+1):
                var1, nvar = get_bool_var(covered, (atom, inv, k), nvar)
                var2, nvar = get_bool_var(rule_use_inv, (rule, inv, k), nvar)
                f.append([-var1, var2])
                if debug_flag:
                    print(f"covered({atom},inv{inv},{k}) -> rule_use_inv({atom},inv{inv},{k})", file=fp_log)
                or_list = []
                or_list_str = []
                for x in range(1, max_pred[pred]+1):
                    var3, nvar = get_bool_var(inv_body_pred, (inv, pred, x), nvar)
                    or_list.append(var3)
                    or_list_str.append(f"inv_body_pred(inv{inv},{pred},{x})")
                f.append([-var1] + or_list)
                if debug_flag:
                    print(f"covered({atom},inv{inv},{k}) -> {' or '.join(or_list_str)}", file=fp_log)
    # Forall(r,k): inv_body_pred(inv,pred,x) -> Sum(covered(atom,inv,k)) <= x
    for inv in range(1, inv_rule_num+1):
        for pred in pred_list:
            for x in range(1, max_pred[pred]+1):
                var1, nvar = get_bool_var(inv_body_pred, (inv, pred, x), nvar)
                for rule in rule_list:
                    for k in range(1, max_use+1):
                        sum_list = []
                        sum_list_str = []
                        for atom in bk["rule"][rule]["body"]:
                            if bk["atom"][atom]["pred"] == pred:
                                var2, nvar = get_bool_var(covered, (atom, inv, k), nvar)
                                sum_list.append(var2)
                                sum_list_str.append(f"covered({atom},inv{inv},{k})")
                        if len(sum_list) > 0:
                            clauses, nvar = get_atmost_encoding(sum_list, [1]*len(sum_list), x, nvar)
                            for c in clauses:
                                f.append([-var1] + c)
                            if debug_flag:
                                print(f"inv_body_pred(inv{inv},{pred},{x}) -> ({' + '.join(sum_list_str)}) <= {x}", file=fp_log)
    # is_covered(atom) <-> Exists.(inv,k): covered(atom,inv,k)
    for atom in atom_list:
        var1, nvar = get_bool_var(is_covered, atom, nvar)
        or_list = []
        or_list_str = []
        for inv in range(1, inv_rule_num+1):
            for k in range(1, max_use+1):
                var2, nvar = get_bool_var(covered, (atom, inv, k), nvar)
                # f.append([var1, -var2])
                or_list.append(var2)
                or_list_str.append(f"covered({atom},inv{inv},{k})")
        f.append([-var1] + or_list)
        if debug_flag:
            print(f"is_covered({atom}) <-> {' or '.join(or_list_str)}", file=fp_log)

    ### symmetry breaking ###
    # inv_used(inv) -> inv_used(inv-1) // make it worse!
    # for inv in range(2, inv_rule_num+1):
    #     var1, nvar = get_bool_var(inv_used, inv, nvar)
    #     var2, nvar = get_bool_var(inv_used, inv-1, nvar)
    #     f.append([-var1, var2])
    #     if debug_flag:
    #         print(f"inv_used(inv{inv}) -> inv_used(inv{inv-1})", file=fp_log)
    
    # inv_used(inv) <-> Exists(pred,x): inv_body_pred(inv,pred,x)
    # for inv in range(1, inv_rule_num+1):
    #     var1, nvar = get_bool_var(inv_used, inv, nvar)
    #     or_list = []
    #     or_list_str = []
    #     for pred in pred_list:
    #         for x in range(1, max_pred[pred]+1):
    #             var2, nvar = get_bool_var(inv_body_pred, (inv, pred, x), nvar)
    #             f.append([var1, -var2])
    #             if debug_flag:
    #                 print(f"inv_body_pred(inv{inv},{pred},{x}) -> inv_used(inv{inv})", file=fp_log)
    #             or_list.append(var2)
    #             or_list_str.append(f"inv_body_pred(inv{inv},{pred},{x})")
    #     f.append([-var1] + or_list)
    #     if debug_flag:
    #         print(f"inv_used(inv{inv}) -> {' or '.join(or_list_str)}", file=fp_log)
    
    ### objective ###
    # inv_used(inv), cost=1
    for inv in range(1, inv_rule_num+1):
        var1, nvar = get_bool_var(inv_used, inv, nvar)
        f.append([-var1], weight=1)
    # inv_body_pred(inv,pred,x), cost=x
    for inv in range(1, inv_rule_num+1):
        for pred in pred_list:
            for x in range(1, max_pred[pred]+1):
                var1, nvar = get_bool_var(inv_body_pred, (inv, pred, x), nvar)
                f.append([-var1], weight=x)
    # rule_use_inv(r,inv,k), cost=1
    for rule in rule_list:
        for inv in range(1, inv_rule_num+1):
            for k in range(1, max_use+1):
                var1, nvar = get_bool_var(rule_use_inv, (rule, inv, k), nvar)
                f.append([-var1], weight=1)
    # is_covered(atom), cost=-1
    for atom in atom_list:
        var1, nvar = get_bool_var(is_covered, atom, nvar)
        f.append([var1], weight=1)
    
    ### solve ###
    print(f"MaxSAT solving... ({f.nv} vars, {len(f.hard)} hard, {len(f.soft)} soft)", flush=True)
    
    cost, model = anytime_maxsat_solve(f.hard, f.soft, f.wght, timeout, solver, 15, solver_args)
    if model is not None:
        # print(f"cost={cost}; mdl={model}")
        model = set(model)
    else:
        raise Exception("MaxSAT solver failed")

    ### parse model ###
    pred_arity = {}
    for atom in atom_list:
        pred = bk["atom"][atom]["pred"]
        pred_arity[pred] = len(bk["atom"][atom]["args"])
    refactored_bk = {"rule": {}, "atom": {}}
    # parse inv rules
    for inv_rule in range(1, inv_rule_num+1):
        rule = f"inv{inv_rule}"
        refactored_bk["rule"][rule] = {"head_pred": rule, "head_args": [], "body": []}
        body_atom_id = 1
        body_arg_id = 1
        for pred in pred_list:
            for x in range(1, max_pred[pred]+1):
                if inv_body_pred[(inv_rule, pred, x)] in model:
                    for k in range(x):
                        atom, body_atom_id = f"{rule}a{body_atom_id}", body_atom_id + 1
                        refactored_bk["rule"][rule]["body"].append(atom)
                        refactored_bk["atom"][atom] = {"pred": pred, "args": []}
                        for _ in range(pred_arity[pred]):
                            arg, body_arg_id = get_new_arg(body_arg_id, pred_list)
                            refactored_bk["atom"][atom]["args"].append(arg)
                            refactored_bk["rule"][rule]["head_args"].append(arg)
    # parse normal rules
    for rule in rule_list:
        refactored_bk["rule"][rule] = {"head_pred": bk["rule"][rule]["head_pred"], "head_args": bk["rule"][rule]["head_args"], "body": []}
        inv_atoms_to_instanciate = {}
        for inv in range(1, inv_rule_num+1):
            for k in range(1, max_use+1):
                if rule_use_inv[(rule, inv, k)] in model:
                    # add inv usage to rule body
                    atom = f"{rule}inv{inv}use{k}"
                    refactored_bk["rule"][rule]["body"].append(atom)
                    refactored_bk["atom"][atom] = {"pred": f"inv{inv}", "args": [], "args_map": {}}
                    for arg_from in refactored_bk["rule"][f"inv{inv}"]["head_args"]:
                        refactored_bk["atom"][atom]["args_map"][arg_from] = None
                    for inv_atom in refactored_bk["rule"][f"inv{inv}"]["body"]:
                        pred = refactored_bk["atom"][inv_atom]["pred"]
                        if pred not in inv_atoms_to_instanciate:
                            inv_atoms_to_instanciate[pred] = []
                        inv_atoms_to_instanciate[pred].append((inv, k, inv_atom))
        for atom in bk["rule"][rule]["body"]:
            pred = bk["atom"][atom]["pred"]
            # not possbile to instanciate, add atom to rule body
            if pred not in inv_atoms_to_instanciate or len(inv_atoms_to_instanciate[pred]) == 0:
                refactored_bk["rule"][rule]["body"].append(atom)
                refactored_bk["atom"][atom] = {"pred": pred, "args": bk["atom"][atom]["args"]}
                continue
            # instanciate inv usage atom
            inv, use, inv_atom = inv_atoms_to_instanciate[pred].pop(0)
            inv_use_atom = f"{rule}inv{inv}use{use}"
            for arg_from, arg_to in zip(refactored_bk["atom"][inv_atom]["args"], bk["atom"][atom]["args"]):
                assert refactored_bk["atom"][inv_use_atom]["args_map"][arg_from] is None
                refactored_bk["atom"][inv_use_atom]["args_map"][arg_from] = arg_to
        # instanciate redundant inv usage atoms
        for pred in inv_atoms_to_instanciate:
            while len(inv_atoms_to_instanciate[pred]) > 0:
                inv, use, inv_atom = inv_atoms_to_instanciate[pred].pop(0)
                inv_use_atom = f"{rule}inv{inv}use{use}"
                for atom in bk["rule"][rule]["body"]:
                    if bk["atom"][atom]["pred"] == pred:
                        for arg_from, arg_to in zip(refactored_bk["atom"][inv_atom]["args"], bk["atom"][atom]["args"]):
                            assert refactored_bk["atom"][inv_use_atom]["args_map"][arg_from] is None
                            refactored_bk["atom"][inv_use_atom]["args_map"][arg_from] = arg_to
                        break
        for inv in range(1, inv_rule_num+1):
            for k in range(1, max_use+1):
                inv_use_atom = f"{rule}inv{inv}use{k}"
                if inv_use_atom in refactored_bk["rule"][rule]["body"]:
                    for arg in refactored_bk["rule"][f"inv{inv}"]["head_args"]:
                        refactored_bk["atom"][inv_use_atom]["args"].append(refactored_bk["atom"][inv_use_atom]["args_map"][arg])
    return refactored_bk
