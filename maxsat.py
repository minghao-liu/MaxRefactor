import subprocess, tempfile, time

from pysat.formula import WCNF
from pysat.examples.rc2 import RC2

def old_wcnf_to_file(hard_clauses, soft_clauses, weights, file):
    n_vars = 0
    for clause in hard_clauses:
        n_vars = max(n_vars, max([abs(lit) for lit in clause]))
    for clause in soft_clauses:
        n_vars = max(n_vars, max([abs(lit) for lit in clause]))
    n_clauses = len(hard_clauses) + len(soft_clauses) - len([w for w in weights if w == 0])
    top = sum(weights)+1
    file.write("p wcnf " + str(n_vars) + " " + str(n_clauses) + " " + str(top) + "\n")
    for clause in hard_clauses:
        #print(str(top) + " " + " ".join(map(str, clause)) + " 0")
        file.write(str(top) + " " + " ".join(map(str, clause)) + " 0" + "\n")
    for clause, w in zip(soft_clauses, weights):
        if w == 0:
            continue
        #print(str(w) + " " + " ".join(map(str, clause)) + " 0")
        file.write(str(w) + " " + " ".join(map(str, clause)) + " 0" + "\n")
    file.flush()

def exact_maxsat_solve(hard_clauses, soft_clauses, weights, solver, solver_args=None):
    if solver == "rc2":
        rc2 = RC2(WCNF())
        for clause in hard_clauses:
            rc2.add_clause(clause)
        for clause, w in zip(soft_clauses, weights):
            if w == 0:
                continue
            rc2.add_clause(clause, weight=w)
        model = rc2.compute()
        if model is not None:
            return rc2.cost, model
        return float("inf"), None
    else:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".wcnf") as tmp:
            old_wcnf_to_file(hard_clauses, soft_clauses, weights, tmp)
            try:
                args = [solver] + (solver_args.split() if solver_args else []) + [tmp.name]
                output = subprocess.check_output(args).decode("utf-8").split("\n")
            except subprocess.CalledProcessError as error:
                output = error.output.decode("utf-8").split("\n")
        if "UNSATISFIABLE" in output:
            return float("inf"), None
        elif "s OPTIMUM FOUND" in output:
            cost_line = [line for line in output if line.startswith("o ")][-1]
            cost = int(cost_line.replace("o ", ""))
            model_line = [line for line in output if line.startswith("v ")][-1]
            model_line = model_line.replace("v ", "")
            model = [i if model_line[i-1] == "1" else -i for i in range(1, len(model_line)+1)]
            return cost, model
        else:
            # print("ERROR: No optimal solution found.")
            #for line in output:
            #   print(line)
            return None, None

def anytime_maxsat_solve(hard_clauses, soft_clauses, weights, timeout, solver, solver_signal, solver_args=None):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".wcnf") as tmp:
        old_wcnf_to_file(hard_clauses, soft_clauses, weights, tmp)
        try:
           output = subprocess.check_output(["timeout", "-s", str(solver_signal), str(timeout), solver] + (solver_args.split() if solver_args else []) + [tmp.name]).decode("utf-8").split("\n")
        except subprocess.CalledProcessError as error:
            output = error.output.decode("utf-8").split("\n")
    if "UNSATISFIABLE" in output:
        return float("inf"), None
    elif "s OPTIMUM FOUND" in output or "s SATISFIABLE" in output:
        cost_line = [line for line in output if line.startswith("o ")][-1]
        cost = int(cost_line.replace("o ", ""))
        if solver == "uwrmaxsat":
            model_line = ""
            for line in output:
                if line.startswith("v "):
                    model_line += line
            model_line = model_line.replace("v ", "")
            model = [i if model_line[i-1] == "1" else -i for i in range(1, len(model_line)+1)]
        else:
            model_line = [line for line in output if line.startswith("v ")][-1]
            model_line = model_line.replace("v ", "")
            model = [i if model_line[i-1] == "1" else -i for i in range(1, len(model_line)+1)]
        return cost, model
    else:
        # print("WARNING: No solution found.")
        #for line in output:
        #   print(line)
        return None, None
