-- Many many thanks to Rob Lewis for supplying 99.9% of this file.

-- modded induction', cases', rw'
-- *TODO* -- waiting for simon PR for symmetry'

import tactic.interactive
import tactic.apply

run_cmd mk_simp_attr `leakage

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr

private meta def resolve_name' (n : name) : tactic expr :=
do {
  p ← resolve_name n,
  match p with
  | expr.const n _ := mk_const n -- create metavars for universe levels
  | _              := i_to_expr p
  end
}

private meta def rw_goal (cfg : rewrite_cfg) (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, rewrite_target e {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_target e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || to_bool (t = h)

private meta def rw_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (not (uses_hyp e hyp)) $ rewrite_hyp e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewrite_hyp e hyp {symm := r.symm, ..cfg} >>= rw_hyp rs)
    (eq_lemmas.empty)

private meta def rw_core (rs : parse rw_rules) (loca : parse location) (cfg : rewrite_cfg) : tactic unit :=
match loca with
| loc.wildcard := loca.try_apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
| _            := loca.apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
end >> (returnopt rs.end_pos >>= save_info <|> skip)

meta def rw' (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
propagate_tags (rw_core q l cfg)

meta def use' (l : parse pexpr_list_or_texpr) : tactic unit :=
tactic.use l

end interactive
end tactic

namespace tactic.interactive

open tactic.interactive interactive.types expr lean lean.parser tactic interactive

meta def induction' (hp : parse cases_arg_p) (rec_name : parse using_ident) 
  (ids : parse with_ident_list) (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do tactic.interactive.induction hp rec_name ids revert,
all_goals `[try { dsimp only with leakage at * }]

--meta def induction' (hp : parse cases_arg_p) (ids : parse with_ident_list) : tactic unit :=
--do tactic.interactive.induction hp none ids none,
--all_goals `[
--  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
--  try {change mynat.le with (≤) at *}]
--  try {change @mynat.succ with (λ n, n + 1) at *, dsimp only at *}]


meta def cases' (hp : parse cases_arg_p) (ids : parse with_ident_list) : tactic unit :=
do tactic.interactive.cases hp ids,
all_goals `[try { dsimp only with leakage at * }]


--meta def cases' : parse cases_arg_p → parse with_ident_list → tactic unit
--| (none,   p) ids := do
--  e ← i_to_expr p,
--  cases_core e ids,
--  all_goals `[
--  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
--  try {rw' (show mynat.le = (≤), from rfl) at *}
--  ]
--| (some h, p) ids := do
--  x   ← get_unused_name,
--  generalize h () (p, x),
--  hx  ← get_local x,
--  cases_core hx ids,
--  all_goals `[
--  try {rw' (show mynat.zero = (0 : mynat), from rfl) at *},
--  try {rw' (show mynat.le = (≤), from rfl) at *}]

-- next def is waiting on https://github.com/leanprover-community/mathlib/pull/1269
--meta def  := symmetry' -- already there

end tactic.interactive

open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `nat_num_game.interactive

@[reducible] meta def filter (d : declaration) : bool :=
d.to_name ∉ [`tactic.interactive.induction, 
             `tactic.interactive.cases, 
             `tactic.interactive.rw, 
             `tactic.interactive.symmetry,
             `tactic.interactive.use]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive ∧ filter dec) (copy_decl dec)

@[reducible] meta def nat_num_game := tactic

namespace nat_num_game

--meta instance : monad nat_num_game := by delta nat_num_game; apply_instance

--meta instance : alternative nat_num_game := by delta nat_num_game; apply_instance

meta def step {α} (c : nat_num_game α) : nat_num_game unit := 
c >> return ()

meta def istep := @tactic.istep

meta def save_info := tactic.save_info

meta def execute (c : nat_num_game unit) : nat_num_game unit := 
c

meta def execute_with := @smt_tactic.execute_with
--meta def trace_state {α : Type}

meta def solve1 := @tactic.solve1

end nat_num_game

--#check tactic.interactive.induction

namespace nat_num_game.interactive

meta def induction
:= tactic.interactive.induction'

meta def cases
:= tactic.interactive.cases'

meta def rw
:= tactic.interactive.rw'

meta def symmetry
:= tactic.interactive.symmetry'

meta def use
:= tactic.interactive.use'

end nat_num_game.interactive

run_cmd copy_decls

--TODO : why is this broken?
--#print tactic.interactive.rintro

--#exit

-- example just to check it's running
-- example (n : ℕ) : true :=
-- begin [nat_num_game]
--   induction n,
--     sorry, sorry  
-- end
