import Holant.Proofs.Tractability.EOEvaluation.PairingTemplates
import Holant.Tractable.AffineOperations


namespace Holant.LocalDrafts.Tractability.EOEvaluation.PairLift
open Holant.Tractable
open scoped BigOperators
noncomputable section
variable {n : ℕ} (p : OrientedPerfectPairing n)

abbrev Word (n : ℕ) := Fin n → Bool
def Compatible (x : Word n) : Prop := ∀ j, x (p.ports (j, false)) ≠ x (p.ports (j, true))

instance compatibleDecidable (x : Word n) : Decidable (Compatible p x) := by
  unfold Compatible
  infer_instance

def compress (x : Word n) : Word p.count := fun j => x (p.ports (j, false))
def indicator : Signature AlgebraicComplex n := fun x => if Compatible p x then 1 else 0
def restrict (g : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => if Compatible p x then g x else 0

theorem word_compress (x : Word n) (hx : Compatible p x) : p.word (compress p x) = x := by
  funext k
  obtain ⟨⟨j, b⟩, rfl⟩ := p.ports.surjective k
  cases b
  · simp [OrientedPerfectPairing.word, compress]
  · have h := hx j
    cases h0 : x (p.ports (j, false)) <;> cases h1 : x (p.ports (j, true)) <;>
      simp_all [OrientedPerfectPairing.word, compress]

theorem lift_identity (g : Signature AlgebraicComplex n) :
    restrict p g = fun x => p.restrict g (compress p x) * indicator p x := by
  funext x
  by_cases h : Compatible p x
  · simp [restrict, indicator, h, OrientedPerfectPairing.restrict, word_compress p x h]
  · simp [restrict, indicator, h]

def system : AffineSystem n where
  rows := p.count
  matrix r j := (if j = p.ports (r, false) then 1 else 0) +
    (if j = p.ports (r, true) then 1 else 0)
  rhs _ := 1

theorem system_holds (x : Word n) : (system p).Holds x ↔ Compatible p x := by
  unfold AffineSystem.Holds Compatible
  apply forall_congr'; intro j
  simp only [system, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  cases x (p.ports (j, false)) <;> cases x (p.ports (j, true)) <;> decide

theorem indicator_affine : Affine (indicator p) := by
  change Affine (fun x : Word n => if Compatible p x then (1 : AlgebraicComplex) else 0)
  simpa only [system_holds] using affine_indicator (system p)

theorem indicator_product : Product (indicator p) := by
  let factors : List (ProductFactor n) := List.ofFn (fun j : Fin p.count =>
    .disequality (p.ports (j, false)) (p.ports (j, true)))
  convert product_formula 1 factors using 1
  funext x
  change (if Compatible p x then (1 : AlgebraicComplex) else 0) =
    1 * (factors.map (fun h => h.eval x)).prod
  simp only [factors, List.map_ofFn, List.prod_ofFn, one_mul, ProductFactor.eval]
  by_cases hx : Compatible p x
  · have hn (j : Fin p.count) := hx j
    simp [hx, hn, Signature.disequality]
  · obtain ⟨j, hj⟩ := not_forall.mp hx
    rw [if_neg hx]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Signature.disequality, not_ne_iff.mp hj])

def renameFactor {m k : ℕ} (indices : Fin k → Fin m) : ProductFactor k → ProductFactor m
  | .unary j u hu => .unary (indices j) u hu
  | .equality i j => .equality (indices i) (indices j)
  | .disequality i j => .disequality (indices i) (indices j)

theorem rename_eval {m k : ℕ} (indices : Fin k → Fin m) (f : ProductFactor k) (x : Word m) :
    (renameFactor indices f).eval x = f.eval (fun j => x (indices j)) := by cases f <;> rfl

theorem product_coordinates {m k : ℕ} (indices : Fin k → Fin m)
    {g : Signature AlgebraicComplex k} (hg : Product g) : Product (fun x => g (fun j => x (indices j))) := by
  rcases hg with hg | ⟨c, hc, fs, rfl⟩
  · rw [hg]; exact product_zero m
  · convert product_formula c (fs.map (renameFactor indices)) using 1
    funext x
    have he : (fun h : ProductFactor k => (renameFactor indices h).eval x) =
        (fun h => h.eval (fun j => x (indices j))) := by
      funext h
      exact rename_eval indices h x
    simp only [productFormula, List.map_map, Function.comp_def, he]

theorem affine_lift {g : Signature AlgebraicComplex n} (hg : Affine (p.restrict g)) : Affine (restrict p g) := by
  rw [lift_identity]
  exact (hg.precompose (compress p) (coordinates_isAffineMap (fun j => p.ports (j, false)))).mul
    (indicator_affine p)

theorem product_lift {g : Signature AlgebraicComplex n} (hg : Product (p.restrict g)) : Product (restrict p g) := by
  rw [lift_identity]
  exact (product_coordinates (fun j => p.ports (j, false)) hg).mul (indicator_product p)

theorem class_lift (C : EOClass) {g : Signature AlgebraicComplex n} (hg : C.Holds (p.restrict g)) :
    C.Holds (restrict p g) := by
  cases C
  · exact affine_lift p hg
  · exact product_lift p hg

end
end Holant.LocalDrafts.Tractability.EOEvaluation.PairLift
