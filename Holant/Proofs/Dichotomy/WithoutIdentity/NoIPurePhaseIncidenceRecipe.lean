import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseAnchorRecipe

/-! The two proper-face correction slots preserve a genuinely bad corrected
logical row. Together with their exact signed-incidence certificate, they
produce three original-row substitutions whose uncorrected coefficient
product is nonaffine. No compressed logical row is installed as a resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceRecipe
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace A
export NoIPurePhaseIncidenceCore.C (codeSeven)
export NoIPurePhaseAnchorRecipe.A (codeSeven_affine)
export NoIPurePhaseAnchorRecipe (corrected)
end A
namespace P
export NoIPurePhaseIncidencePorts.P (Transform linearWord)
export NoIPurePhaseIncidencePorts.R (transformed transformed_word)
export NoIPurePhaseIncidencePorts (rows rows_zero)
end P
namespace W
export NoIPurePhaseIncidenceWeight (residue)
end W
namespace R
export NoIPurePhaseRecipeFactor (factor total mul_iff)
export NoIPurePhaseIncidenceRegularization (Corrects)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n : ℕ}

def product (f : Signature AlgebraicComplex n) (p : Fin n→Port 7) (q : Fin 2→P.Transform) :
    Signature AlgebraicComplex 7 := fun z=>∏i : Fin 3,f (word (P.rows p q i) z)

theorem corrected_value (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (p : Fin n→Port 7) (q : Fin 2→P.Transform) (z : Fin 7→Bool) :
    product (A.corrected r f) p q z=product f p q z*R.factor (P.rows p q) r z := by
  simp only [product,A.corrected,R.factor,
    Finset.prod_mul_distrib]
  exact mul_comm _ _

theorem product_bad (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (f : Signature AlgebraicComplex n) (p : Fin n→Port 7) (q : Fin 2→P.Transform)
    (corrects : R.Corrects (W.residue p) q)
    (full : ∀x : Fin 3→Bool,f (word p (A.codeSeven x))≠0)
    (bad : ¬Affine (fun x : Fin 3→Bool=>A.corrected r f (word p (A.codeSeven x))))
    (faces : ∀i : Fin 2,Affine (fun x : Fin 3→Bool=>
      A.corrected r f (word p (A.codeSeven (P.linearWord (q i) x))))) :
    ¬Affine (product f p q) := by
  let multiplier : Signature AlgebraicComplex 3:=fun x=>
    ∏i : Fin 2,A.corrected r f (word p (A.codeSeven (P.linearWord (q i) x)))
  have good : Affine multiplier := by
    simpa only [multiplier,Fin.prod_univ_two] using (faces 0).mul (faces 1)
  have nonzero (x : Fin 3→Bool) : multiplier x≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact mul_ne_zero (pow_ne_zero _ rn) (full _)
  intro affine
  have corrected:=(R.mul_iff (P.rows p q) r rn root
    (fun j=>P.rows_zero p q corrects j) (product f p q)).mpr affine
  have eqn : (fun z=>product f p q z*R.factor (P.rows p q) r z)=product (A.corrected r f) p q :=
    funext (fun z=>(corrected_value r f p q z).symm)
  rw [eqn] at corrected
  have pull:=corrected.precompose A.codeSeven A.codeSeven_affine
  apply bad
  apply (NoIPureAffineMultiplier.mul_iff _ multiplier good (fun x _=>nonzero x)).mp
  simpa only [product,Fin.prod_univ_succ,P.rows,Fin.cases_zero,Fin.cases_succ,
    P.transformed_word,multiplier] using pull

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceRecipe
end
