import argparse

def parse_bk_from_file(bk_filename):
    def get_pred_and_args(atom):
        pred, args = atom.split("(")
        args = args[:-1].split(",")
        return pred, args
    
    bk_raw = []
    with open(bk_filename, "r") as fin:
        for line in fin:
            line = line.strip().replace(" ", "")
            head, body = line.split(":-")
            body = body.replace(".", "")
            body_atoms = []
            atom = ""
            pcnt = 0
            for ch in body:
                if ch == "," and pcnt == 0:
                    body_atoms.append(atom)
                    atom = ""
                else:
                    atom += ch
                    if ch == "(":
                        pcnt += 1
                    elif ch == ")":
                        pcnt -= 1
            body_atoms.append(atom)
            bk_raw.append((head, body_atoms))
    bk = {"rule": {}, "atom": {}}
    for i, (head, body_atoms) in enumerate(bk_raw):
        head_pred, head_args = get_pred_and_args(head)
        rule, pred, arity = f'r{i+1}', head_pred, len(head_args)
        bk["rule"][rule] = {"head_pred": pred,
                            "head_args": [None for _ in range(arity)],
                            "body": []}
        for j, arg in enumerate(head_args):
            rule, arg_id, arg = f'r{i+1}', j+1, arg
            bk["rule"][rule]["head_args"][arg_id-1] = arg
        for j, body_atom in enumerate(body_atoms):
            body_pred, body_args = get_pred_and_args(body_atom)
            rule, atom, pred, arity = f'r{i+1}', f'r{i+1}a{j+1}', body_pred, len(body_args)
            assert rule in bk["rule"] and atom not in bk["atom"]
            bk["rule"][rule]["body"].append(atom)
            bk["atom"][atom] = {"pred": pred, "args": [None for _ in range(arity)]}
            for k, arg in enumerate(body_args):
                rule, atom, arg_id, arg = f'r{i+1}', f'r{i+1}a{j+1}', k+1, arg
                bk["atom"][atom]["args"][int(arg_id)-1] = arg
    return bk

def print_bk(bk):
    n_rules = 0
    size = 0
    for rule in bk["rule"]:
        if len(bk["rule"][rule]["body"]) > 0:
            n_rules += 1
            size += len(bk["rule"][rule]["body"]) + 1
    print("number of rules:", n_rules, flush=True)
    print(f"program size:", size, flush=True)
    for rule in bk["rule"]:
        head_atom = bk["rule"][rule]["head_pred"] + "(" + ",".join(bk["rule"][rule]["head_args"]) + ")"
        print(f"({rule}) {head_atom} :- ", end="")
        body_atoms = []
        for atom in bk["rule"][rule]["body"]:
            body_atom = bk["atom"][atom]["pred"] + "(" + ",".join(bk["atom"][atom]["args"]) + ")"
            body_atoms.append(body_atom)
        print(", ".join(body_atoms) + ".", flush=True)
    print("=" * 20, flush=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--bk", type=str, default="data/demo.pl")
    parser.add_argument("--inv-rule-num", type=int, default=1)
    parser.add_argument("--solver", choices=["cpsat", "maxsat"], default="cpsat")
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()

    bk_rules = parse_bk_from_file(args.bk)
    print_bk(bk_rules)
    
    if args.solver == "cpsat":
        from solve_cpsat import do_compression
    else:
        from solve_maxsat import do_compression
    refactored_bk_rules = do_compression(bk_rules, args)
    
    print_bk(refactored_bk_rules)
