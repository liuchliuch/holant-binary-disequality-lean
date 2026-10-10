import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.WordLookup


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.FiniteDispatch

open Computability Holant.Complexity BinaryCompose FixedFieldMachines
open AffineMachine FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
set_option backward.isDefEq.respectTransparency false

def select {A B : Type} {n : ℕ} (key : A → ℕ) (f : A → Fin n → B) (fallback : A → B) :
    List (Fin n) → A → B
  | [], a => fallback a
  | i :: is, a => if key a = i.val then f a i else select key f fallback is a

theorem select_at {A B : Type} {n : ℕ} (key : A → ℕ) (f : A → Fin n → B) (fallback : A → B)
    (is : List (Fin n)) (i : Fin n) (hi : i ∈ is) (a : A) (ha : key a = i.val) :
    select key f fallback is a = f a i := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    by_cases hj : key a = j.val
    · have he : j = i := Fin.ext (hj.symm.trans ha)
      simp [select, hj, he]
    · have hm : i ∈ js := by
        rcases List.mem_cons.mp hi with h | h
        · subst j; exact False.elim (hj ha)
        · exact h
      simp only [select, if_neg hj]
      exact ih hm

noncomputable def computes {A B : Type} {n : ℕ} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (key : A → ℕ) (f : A → Fin n → B) (fallback : A → B)
    (wk : Computes ea encodingNatBool key) (wf : ∀ i, Computes ea eb (fun a => f a i))
    (wd : Computes ea eb fallback) :
    (is : List (Fin n)) → Computes ea eb (select key f fallback is)
  | [] => wd
  | i :: is => congrComputes (ifComputes
      (AccessPrograms.eqNat wk (constantComputes ea encodingNatBool i.val)) (wf i)
      (computes ea eb key f fallback wk wf wd is)) (fun a => by simp [select])

end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.FiniteDispatch
