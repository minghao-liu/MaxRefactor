import argparse, os, time


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--domain", choices=['strings', 'lego', 'realworld'], required=True)
    args = parser.parse_args()

    domains = [args.domain]
    if args.domain == 'strings' or args.domain == 'lego':
        timeouts = [600]
    else:
        timeouts = [3600]
    inv_rule_nums = [2]
    solvers = ['cpsat', 'maxsat']
    
    for solver in solvers:
        for domain in domains:
            runtime_log = open(f"log/{domain}-{solver}/runtime.log", 'a')
            for filename in os.listdir(f'data/{domain}'):
                if filename.endswith('.pl'):
                    bk_file = f'data/{domain}/{filename}'
                    for inv_rule_num in inv_rule_nums:
                        for timeout in timeouts:
                            log_path = f"log/{domain}-{solver}/{filename}_{inv_rule_num}inv_{timeout}s.log"
                            if os.path.exists(log_path):
                                print(f"[SKIP] experiment {log_path} already exists", flush=True)
                                continue
                            cmd = f"python maxrefactor.py --bk {bk_file} --solver={solver} --inv-rule-num={inv_rule_num} --timeout={timeout} > {log_path}"
                            print(f"[RUN] {cmd}", flush=True)
                            t1 = time.perf_counter()
                            os.system(cmd)
                            t2 = time.perf_counter()
                            print(f"{log_path}\t{t2 - t1}", file=runtime_log, flush=True)
            runtime_log.close()
