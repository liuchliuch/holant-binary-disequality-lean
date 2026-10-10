import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionCircuit
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSparseWeightRecipe
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRetraction

/-! Finite literal gadgets with all private Boolean variables explicit.
Tracing one exposed variable is an actual permutation of the stored ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget
open Holant Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate evaluate_compose)
end B
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose)
end I
namespace R
export GeneralEOPairedFamilyExtractionRecipe (Recipe denote Bad)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

structure Gadget (n m : ℕ) where
  privateCount : ℕ
  ports : List (Fin n → Bool ⊕ Fin (m+privateCount))

variable {n m : ℕ}

def denote {K : Type*} [CommSemiring K] (f : Signature K n) (g : Gadget n m) : Signature K m :=
  fun z=>∑y : Word g.privateCount,B.evaluate f g.ports (Fin.addCases z y)

def direct (ps : List (Fin n → Bool ⊕ Fin m)) : Gadget n m := ⟨0,ps⟩

theorem direct_value {K : Type*} [CommSemiring K] (f : Signature K n)
    (ps : List (Fin n → Bool ⊕ Fin m)) (z : Word m) : denote f (direct ps) z=B.evaluate f ps z := by
  unfold denote direct
  simp only [Fintype.sum_unique]
  apply congrArg (B.evaluate f ps)
  funext j
  exact Fin.addCases_left j

def tracePort (m k : ℕ) : Fin ((m+1)+k) → Bool ⊕ Fin (m+(k+1)) :=
  Fin.addCases
    (Fin.lastCases (Sum.inr (Fin.natAdd m 0)) (fun j=>Sum.inr (Fin.castAdd (k+1) j)))
    (fun j=>Sum.inr (Fin.natAdd m j.succ))

def trace (g : Gadget n (m+1)) : Gadget n m :=
  ⟨g.privateCount+1,g.ports.map (fun p=>I.compose p (tracePort m g.privateCount))⟩

def assignment (k : ℕ) : (Bool×Word k) ≃ Word (k+1) where
  toFun p := Fin.cons p.1 p.2
  invFun y := (y 0,fun j=>y j.succ)
  left_inv := by intro p; cases p; rfl
  right_inv := by intro y; exact Fin.cons_self_tail y

theorem trace_substitute (z : Word m) (b : Bool) {k : ℕ} (y : Word k) :
    T.substitute (tracePort m k) (Fin.addCases z (Fin.cons b y))=Fin.addCases (Fin.snoc z b) y := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · refine Fin.lastCases ?_ (fun j=>?_) j
    · simp [T.substitute,tracePort]
    · simp [T.substitute,tracePort]
  · simp [T.substitute,tracePort]

theorem trace_value {K : Type*} [CommSemiring K] (f : Signature K n)
    (g : Gadget n (m+1)) (z : Word m) :
    denote f (trace g) z=∑b : Bool,denote f g (Fin.snoc z b) := by
  change (∑y : Word (g.privateCount+1),B.evaluate f
    (g.ports.map (fun p=>I.compose p (tracePort m g.privateCount))) (Fin.addCases z y))=_
  let _ : Fintype (Word g.privateCount) := inferInstanceAs (Fintype (Fin g.privateCount → Bool))
  let _ : Fintype (Bool×Word g.privateCount) := inferInstance
  rw [←(assignment g.privateCount).sum_comp,Fintype.sum_prod_type]
  simp only [assignment,Equiv.coe_fn_mk,B.evaluate_compose,trace_substitute]
  rfl

def ofRecipe : R.Recipe n → Gadget n 2
  | .direct ps => direct ps
  | .marginal ps => trace (direct ps)

theorem ofRecipe_value (f : Signature AlgebraicComplex n) (r : R.Recipe n) :
    denote f (ofRecipe r)=R.denote f r := by
  cases r with
  | direct ps => funext z; exact direct_value f ps z
  | marginal ps =>
    funext z
    rw [ofRecipe,trace_value]
    simp only [direct_value,R.denote]

def Bad (f : Signature AlgebraicComplex n) (g : Gadget n 2) : Prop :=
  ¬Affine (denote f g) ∧ ¬Product (denote f g)

theorem ofRecipe_bad (f : Signature AlgebraicComplex n) (r : R.Recipe n) (h : R.Bad f r) :
    Bad f (ofRecipe r) := by
  unfold Bad
  rw [ofRecipe_value]
  exact h

theorem substitute_affine (q : Fin n → Bool ⊕ Fin m) : IsAffineMap (T.substitute q) := by
  intro x y
  funext i
  cases h : q i with
  | inl b => cases b <;> simp [T.substitute,h,AffinePhase.xor]
  | inr j => simp [T.substitute,h,AffinePhase.xor,origin]

theorem affine_comp {k : ℕ} (p : Word n → Word k) (q : Word m → Word n)
    (hp : IsAffineMap p) (hq : IsAffineMap q) : IsAffineMap (fun x=>p (q x)) := by
  intro x y
  dsimp only
  rw [hq x y,hp _ _,hp _ _]
  funext i
  simp only [xor_apply]
  generalize p (q x) i=a
  generalize p (q y) i=b
  generalize p (q (origin m)) i=c
  generalize p (origin n) i=d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget
