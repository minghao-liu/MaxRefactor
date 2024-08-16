from ortools.sat.python import cp_model

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

    debug_flag = False
    if debug_flag:
        fp_log = open("cpsat_debug.log", "w")

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
    total_size = 0
    for rule in bk["rule"]:
        total_size += len(bk["rule"][rule]["body"]) + 1
    atom_rule = {}
    for rule in rule_list:
        for atom in bk["rule"][rule]["body"]:
            atom_rule[atom] = rule
    
    ### variables ###
    n_aux = 0
    mdl = cp_model.CpModel()
    inv_body_pred = {}
    for inv in range(inv_rule_num):
        for pred in pred_list:
            inv_body_pred[(inv, pred)] = mdl.NewIntVar(0, max_pred[pred], f"inv_body_pred(inv{inv},{pred})")
    rule_use_inv = {}
    for rule in rule_list:
        for inv in range(inv_rule_num):
            for use in range(max_use):
                rule_use_inv[(rule, inv, use)] = mdl.NewBoolVar(f"rule_use_inv({rule},inv{inv},{use})")
    inv_used = {}
    for inv in range(inv_rule_num):
        inv_used[inv] = mdl.NewBoolVar(f"inv_used(inv{inv})")
    covered = {}
    for atom in atom_list:
        for inv in range(inv_rule_num):
            for use in range(max_use):
                covered[(atom, inv, use)] = mdl.NewBoolVar(f"covered({atom},inv{inv},{use})")
    is_covered = {}
    for atom in atom_list:
        is_covered[atom] = mdl.NewBoolVar(f"is_covered({atom})")
    
    ### constraints ###
    # rule_use_inv(r,inv,id) /\ inv_body_pred(inv,pred) > 0 -> rule_pred(r,pred) > 0
    for rule in rule_list:
        for pred in pred_list:
            if rule_pred[(rule, pred)] == 0:
                for inv in range(inv_rule_num):
                    for use in range(max_use):
                        aux1, n_aux = mdl.NewBoolVar(f"aux{n_aux}"), n_aux+1
                        mdl.Add(inv_body_pred[(inv, pred)] == 0).OnlyEnforceIf(aux1)
                        mdl.Add(inv_body_pred[(inv, pred)] > 0).OnlyEnforceIf(aux1.Not())
                        mdl.AddBoolOr([rule_use_inv[(rule, inv, use)].Not(), aux1])
                        if debug_flag:
                            print(f"not rule_use_inv({rule},inv{inv},{use}) or inv_body_pred(inv{inv},{pred}) == 0", file=fp_log)
    # inv_used(inv) <-> Exists.(r,id): rule_use_inv(r,inv,id)
    for inv in range(inv_rule_num):
        var1 = inv_used[inv]
        or_list = []
        or_strs = []
        for rule in rule_list:
            for use in range(max_use):
                var2 = rule_use_inv[(rule, inv, use)]
                mdl.AddImplication(var2, var1)
                if debug_flag:
                    print(f"rule_use_inv({rule},inv{inv},{use}) -> inv_used(inv{inv})", file=fp_log)
                or_list.append(var2)
                or_strs.append(f"rule_use_inv({rule},inv{inv},{use})")
        mdl.AddBoolOr(or_list).OnlyEnforceIf(var1)
        if debug_flag:
            print(f"inv_used(inv{inv}) -> {' or '.join(or_strs)}", file=fp_log)
    # rule_use_inv(r,inv,id) -> rule_use_inv(r,inv,id-1)
    for rule in rule_list:
        for inv in range(inv_rule_num):
            for use in range(1, max_use):
                mdl.Add(rule_use_inv[(rule, inv, use)] <= rule_use_inv[(rule, inv, use-1)])
                if debug_flag:
                    print(f"rule_use_inv({rule},inv{inv},{use}) -> rule_use_inv({rule},inv{inv},{use-1})", file=fp_log)
    # covered(atom,inv,id) -> rule_use_inv(atom.r,inv,id) /\ inv_body_pred(inv,atom.pred) > 0
    for atom in atom_list:
        rule = atom_rule[atom]
        pred = bk["atom"][atom]["pred"]
        for inv in range(inv_rule_num):
            for use in range(max_use):
                var1 = covered[(atom, inv, use)]
                var2 = rule_use_inv[(rule, inv, use)]
                aux1, n_aux = mdl.NewBoolVar(f"aux{n_aux}"), n_aux+1
                mdl.Add(inv_body_pred[(inv, pred)] > 0).OnlyEnforceIf(aux1)
                mdl.Add(inv_body_pred[(inv, pred)] == 0).OnlyEnforceIf(aux1.Not())
                mdl.AddBoolAnd([var2, aux1]).OnlyEnforceIf(var1)
                if debug_flag:
                    print(f"covered({atom},inv{inv},{use}) -> rule_use_inv({rule},inv{inv},{use}) and inv_body_pred(inv{inv},{pred}) > 0", file=fp_log)
    # covered(atom,inv1,id1) -> not covered(atom,inv2,id2)
    # for atom in atom_list:
    #     for inv1, id1 in [(inv, id) for inv in range(inv_rule_num) for id in range(max_use)]:
    #         for inv2, id2 in [(inv, id) for inv in range(inv_rule_num) for id in range(max_use)]:
    #             if inv1 != inv2 or id1 != id2:
    #                 mdl.AddImplication(covered[(atom, inv1, id1)], covered[(atom, inv2, id2)].Not())
    #                 if debug_flag:
    #                     print(f"covered({atom},inv{inv1},{id1}) -> not covered({atom},inv{inv2},{id2})", file=fp_log)
    # Forall.(r,id): Sum(covered(r.atom,inv,id)) <= inv_body_pred(inv,pred)
    for inv in range(inv_rule_num):
        for pred in pred_list:
            for rule in rule_list:
                for use in range(max_use):
                    sum_list = []
                    sum_strs = []
                    for atom in bk["rule"][rule]["body"]:
                        if bk["atom"][atom]["pred"] == pred:
                            sum_list.append(covered[(atom, inv, use)])
                            sum_strs.append(f"covered({atom},inv{inv},{use})")
                    if len(sum_list) > 0:
                        mdl.Add(sum(sum_list) <= inv_body_pred[(inv, pred)])
                        if debug_flag:
                            print(f"{' + '.join(sum_strs)} <= inv_body_pred(inv{inv},{pred})", file=fp_log)
    # is_covered(atom) -> Exists.(inv,id): covered(atom,inv,id)
    for atom in atom_list:
        var1 = is_covered[atom]
        or_list = []
        or_strs = []
        for inv in range(inv_rule_num):
            for use in range(max_use):
                var2 = covered[(atom, inv, use)]
                or_list.append(var2)
                or_strs.append(f"covered({atom},inv{inv},{use})")
        mdl.AddBoolOr(or_list).OnlyEnforceIf(var1)
        if debug_flag:
            print(f"is_covered({atom}) -> {' or '.join(or_strs)}", file=fp_log)

    ### objective ###
    # inv_used(inv), cost=1
    obj1 = mdl.NewIntVar(0, inv_rule_num, "obj1")
    mdl.Add(obj1 == sum([inv_used[inv] for inv in range(inv_rule_num)]))
    # inv_body_pred(inv,pred)=x, cost=x
    obj2 = mdl.NewIntVar(0, cp_model.INT32_MAX, "obj2")
    mdl.Add(obj2 == sum([inv_body_pred[(inv, pred)] for inv in range(inv_rule_num) for pred in pred_list]))
    # rule_use_inv(r,inv,use), cost=1
    obj3 = mdl.NewIntVar(0, cp_model.INT32_MAX, "obj3")
    mdl.Add(obj3 == sum([rule_use_inv[(rule, inv, use)] for rule in rule_list for inv in range(inv_rule_num) for use in range(max_use)]))
    # covered(atom), cost=-1
    obj4 = mdl.NewIntVar(0, len(atom_list), "obj4")
    mdl.Add(obj4 == sum([is_covered[atom] for atom in atom_list]))

    mdl.Minimize(total_size + obj1 + obj2 + obj3 - obj4)

    ### solve ###
    print(f"CP-SAT solving...", flush=True)

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.max_time_in_seconds = timeout
    # solver.parameters.log_search_progress = True
    # solution_printer = cp_model.ObjectiveSolutionPrinter()
    # status = solver.SolveWithSolutionCallback(mdl, solution_printer)
    status = solver.Solve(mdl)
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        # print(f"CP-SAT solver found a solution, obj={solver.ObjectiveValue()}", flush=True)
        pass
    else:
        raise Exception("CP-SAT solver failed")

    ### parse model ###
    pred_arity = {}
    for atom in atom_list:
        pred = bk["atom"][atom]["pred"]
        pred_arity[pred] = len(bk["atom"][atom]["args"])
    refactored_bk = {"rule": {}, "atom": {}}
    # parse inv rules
    for inv_rule in range(inv_rule_num):
        rule = f"inv{inv_rule}"
        refactored_bk["rule"][rule] = {"head_pred": rule, "head_args": [], "body": []}
        body_atom_id = 1
        body_arg_id = 1
        for pred in pred_list:
            x = solver.Value(inv_body_pred[(inv_rule, pred)])
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
        for inv in range(inv_rule_num):
            for k in range(max_use):
                if solver.Value(rule_use_inv[(rule, inv, k)]):
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
        for inv in range(inv_rule_num):
            for k in range(max_use):
                inv_use_atom = f"{rule}inv{inv}use{k}"
                if inv_use_atom in refactored_bk["rule"][rule]["body"]:
                    for arg in refactored_bk["rule"][f"inv{inv}"]["head_args"]:
                        refactored_bk["atom"][inv_use_atom]["args"].append(refactored_bk["atom"][inv_use_atom]["args_map"][arg])
    return refactored_bk
