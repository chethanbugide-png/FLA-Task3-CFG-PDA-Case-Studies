# FLA Task 3 — Case Study-Based Analysis and Design using CFG and PDA

**Author:** B. Sai Chethan (`RA2411026050043`)  
**Course:** 21CSC301T – Formal Language and Automata (CLA-2, Task 3)  
**Institution:** SRM Institute of Science and Technology, Tiruchirappalli  

## Case Studies

| Case Study | Language | CFG Status | PDA Type |
| :--- | :--- | :--- | :--- |
| **Infix Arithmetic (`arith`)** | Expressions over `{i, +, *, (, )}` | Ambiguous $\to$ Precedence CFG | 1-state empty-stack NPDA |
| **Balanced Delimiters (`brackets`)** | Nested `()`, `[]`, `{}` | Ambiguous $\to$ Unambiguous CFG | 2-state final-state DPDA |
| **Center-Marked Palindrome (`palindrome`)** | $\{ w c w^R : w \in \{a,b\}^* \}$ | Unambiguous CFG | 3-state final-state DPDA |

## Usage

Requires Node.js (tested on v24+).

```bash
# Run all 30 report cases, PDA vs. CFG vs. oracle checks, and ambiguity checks
node pda_cfg_studies.js test

# Run combined accept/reject trace demo for all three studies
node pda_cfg_studies.js demo

# Trace PDA configurations for an individual string
node pda_cfg_studies.js trace arith "i+i*i"
node pda_cfg_studies.js trace brackets "([]){}"
node pda_cfg_studies.js trace palindrome "abcba"

# Display original and revised grammars
node pda_cfg_studies.js grammar arith
node pda_cfg_studies.js grammar brackets

# Run bounded ambiguity detector across short strings
node pda_cfg_studies.js ambiguity
```
