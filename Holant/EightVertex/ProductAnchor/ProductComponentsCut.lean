import Holant.EightVertex.ProductAnchor.ProductComponentsSupport
import Holant.TensorClosure
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-! A disconnected product-factor graph gives two actual disjoint coordinate
factors, with explicit finite block ports and the original nonzero scalar. -/
namespace Holant.EightVertex.ProductAnchor
open Holant Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def primaryPort : ProductFactor n → Fin n
  | .unary j _ _ => j
  | .equality j _ => j
  | .disequality j _ => j

def CutClosed (ps : List (ProductFactor n)) (C : Fin n → Bool) : Prop :=
  ∀ i j, FactorLinked ps i j → C i = C j

def extendCut (C : Fin n → Bool) (b : Bool) (y : {i // C i = b} → Bool) : Fin n → Bool :=
  fun i => if h : C i = b then y ⟨i,h⟩ else false

def cutPiece (ps : List (ProductFactor n)) (C : Fin n → Bool) (b : Bool)
    (y : {i // C i = b} → Bool) : AlgebraicComplex :=
  (ps.map (fun p => if C (primaryPort p) = b then p.eval (extendCut C b y) else 1)).prod

def cutProduct (ps : List (ProductFactor n)) (C : Fin n → Bool) (b : Bool)
    (x : Fin n → Bool) : AlgebraicComplex :=
  (ps.map (fun p => if C (primaryPort p) = b then p.eval x else 1)).prod

theorem factor_eval_extendCut (ps : List (ProductFactor n)) (C : Fin n → Bool)
    (hc : CutClosed ps C) (b : Bool) (x : Fin n → Bool)
    (p : ProductFactor n) (hp : p ∈ ps) (hb : C (primaryPort p) = b) :
    p.eval (extendCut C b (fun i => x i)) = p.eval x := by
  cases p with
  | unary j u hu =>
    have hj : C j = b := hb
    simp [ProductFactor.eval,extendCut,hj]
  | equality i j =>
    have hi : C i = b := hb
    have hj : C j = b := (hc i j (Or.inl hp)).symm.trans hi
    simp [ProductFactor.eval,extendCut,hi,hj]
  | disequality i j =>
    have hi : C i = b := hb
    have hj : C j = b := (hc i j (Or.inr hp)).symm.trans hi
    simp [ProductFactor.eval,extendCut,hi,hj]

theorem cutPiece_restrict (ps : List (ProductFactor n)) (C : Fin n → Bool)
    (hc : CutClosed ps C) (b : Bool) (x : Fin n → Bool) :
    cutPiece ps C b (fun i => x i) = cutProduct ps C b x := by
  unfold cutPiece cutProduct
  congr 1
  apply List.map_congr_left
  intro p hp
  by_cases hb : C (primaryPort p) = b
  · simp [hb,factor_eval_extendCut ps C hc b x p hp hb]
  · simp [hb]

theorem cutProduct_mul (ps : List (ProductFactor n)) (C : Fin n → Bool) (x : Fin n → Bool) :
    cutProduct ps C false x * cutProduct ps C true x = (ps.map (fun p => p.eval x)).prod := by
  induction ps with
  | nil => simp [cutProduct]
  | cons p ps ih =>
    simp only [cutProduct,List.map_cons,List.prod_cons] at ih ⊢
    cases h : C (primaryPort p) <;> simp only [Bool.false_eq_true,Bool.true_eq_false,
      ite_true,ite_false,one_mul] <;> rw [←ih] <;> ring

/-- Each Boolean side receives precisely its original-coordinate fiber. -/
def cutArity (C : Fin n → Bool) (v : Fin 2) : ℕ :=
  Fintype.card {i // C i = finTwoEquiv v}

def cutPortEquiv (C : Fin n → Bool) : (Σ v : Fin 2, Fin (cutArity C v)) ≃ Fin n :=
  (Equiv.sigmaCongr finTwoEquiv (fun v => (Fintype.equivFin {i // C i = finTwoEquiv v}).symm)).trans
    (Equiv.sigmaFiberEquiv C)

@[simp] theorem cutPortEquiv_apply (C : Fin n → Bool) (v : Fin 2) (i : Fin (cutArity C v)) :
    cutPortEquiv C ⟨v,i⟩ = ((Fintype.equivFin {j // C j = finTwoEquiv v}).symm i).val := rfl

def cutDecomposition (a : AlgebraicComplex) (ha : a ≠ 0) (ps : List (ProductFactor n))
    (C : Fin n → Bool) : TensorDecomposition AlgebraicComplex n where
  count := 2
  arity := cutArity C
  factor := fun v y => cutPiece ps C (finTwoEquiv v)
    (fun i => y ((Fintype.equivFin {j // C j = finTwoEquiv v}) i))
  ports := cutPortEquiv C
  scale := Units.mk0 a ha

theorem cutDecomposition_value (a : AlgebraicComplex) (ha : a ≠ 0)
    (ps : List (ProductFactor n)) (C : Fin n → Bool) (hc : CutClosed ps C) :
    (cutDecomposition a ha ps C).value = productFormula a ps := by
  funext x
  simp only [TensorDecomposition.value,cutDecomposition,Fin.prod_univ_succ,
    cutPortEquiv_apply,Equiv.symm_apply_apply,Units.val_mk0,Fin.prod_univ_zero,mul_one]
  change a * (cutPiece ps C false (fun i => x i) * cutPiece ps C true (fun i => x i)) = _
  rw [cutPiece_restrict ps C hc,cutPiece_restrict ps C hc,cutProduct_mul]
  rfl

/-- A component's characteristic bit is constant along every factor edge. -/
def componentCut (ps : List (ProductFactor n)) (root : Fin n) : Fin n → Bool :=
  by
    classical
    exact fun i => decide (FactorConnected ps root i)

theorem componentCut_closed (ps : List (ProductFactor n)) (root : Fin n) :
    CutClosed ps (componentCut ps root) := by
  classical
  intro i j h
  simp only [componentCut,decide_eq_decide]
  exact component_closed ps root h

theorem componentCut_root (ps : List (ProductFactor n)) (root : Fin n) :
    componentCut ps root root = true := by
  simp [componentCut,FactorConnected,Relation.EqvGen.refl]

end
end Holant.EightVertex.ProductAnchor
