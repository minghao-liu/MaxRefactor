# MaxRefactor

Code implementation and experimental data of the knowledge refactoring algorithm described in "[Scalable Knowledge Refactoring Using Constrained Optimisation](https://ojs.aaai.org/index.php/AAAI/article/view/33650)", accepted by AAAI 2025.

## Requirements

- [OR-Tools](https://developers.google.com/optimization/install)
- [UWrMaxSat](https://github.com/marekpiotrow/UWrMaxSat) (add to PATH)

## Usage

```
python maxrefactor.py --bk [bk_file] \
                      --solver {cpsat|maxsat} \
                      --inv-rule-num [inv_rule_num] \ 
                      --timeout [timeout]
```
- `bk_file`: path to the knowledge base file.
- `inv_rule_num`: the number of invented rules.
- `timeout`: time limit in seconds.

## Reproducibility

To reproduce our experimental results, run the following command:

```
python run_experiment.py --domain {strings|lego|realworld}
```
