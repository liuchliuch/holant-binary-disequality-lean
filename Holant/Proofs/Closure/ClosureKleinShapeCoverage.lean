import Holant.Proofs.Closure.ClosureKleinShapeGroup
import Holant.Proofs.Closure.ClosureSourceRowsKleinAxis

/-! NEW_POST_RECOVERY actual-key coverage producer, freshly checked before promotion;
final promoted module has its own hash-bound strict acceptance check. Actual noncyclic order-four group data construct standard/exotic raw
representative coverage with nonzero ORIGINAL-field coefficients. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.EqualityQuaternary
open ClosureSourceRowsKleinAxis
variable {L : Type} [Field L]

private theorem map_nonzero (φ : L →+* AlgebraicComplex) {c : L} (hc : c ≠ 0) : φ c ≠ 0 := by
  intro h
  apply hc
  apply φ.injective
  simpa using h

private theorem mapped_smul (φ : L →+* AlgebraicComplex) (c : L) (B : Binary (K:=L)) :
    (c • B).map φ = scale (φ c) (B.map φ) := by
  ext u v
  simp [Matrix.map_apply,Matrix.smul_apply,scale]

private theorem scale_compose (φ : L →+* AlgebraicComplex) (c d : L) (B : Holant.Marked.Mat) :
    scale (φ c) (scale (φ d) B) = scale (φ (c*d)) B := by
  ext u v
  simp [scale,map_mul,mul_assoc]

private theorem E_zero (kind : Klein.Kind) : Klein.E kind 0 = (1 : Binary (K:=AlgebraicComplex)) := by
  cases kind <;> ext u v <;> cases u <;> cases v <;>
    norm_num [Klein.E,Klein.basisQ,Klein.matrix,Matrix.one_apply]

private theorem E_one (kind : Klein.Kind) : Klein.E kind 1 = (X : Binary (K:=AlgebraicComplex)) := by
  cases kind <;> ext u v <;> cases u <;> cases v <;>
    norm_num [Klein.E,Klein.basisQ,Klein.matrix,X,Signature.disequality]

/-- Every represented row multiplier is nonzero in original L, before φ. -/
structure RepresentativeCoverage (φ : L →+* AlgebraicComplex)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (kind : Klein.Kind) : Prop where
  forward : ∀ j : completeGroup F torsion, ∃ k : Fin 4, ∃ c : L,
    c ≠ 0 ∧ (actualRepresentative F torsion j).map φ = scale (φ c) (Klein.E kind k)
  backward : ∀ k : Fin 4, ∃ j : completeGroup F torsion, ∃ c : L,
    c ≠ 0 ∧ (actualRepresentative F torsion j).map φ = scale (φ c) (Klein.E kind k)

variable [CharZero L]

/-- The explicit four ACTUAL keys cover the four literal rows. Product-key
scalars are recovered from actual projective equality in original L. -/
theorem FourSource.representativeCoverage (φ : L →+* AlgebraicComplex)
    {F : SignatureFamily L} {torsion : ResidualTorsion F} {hI : RetainsIdentity F}
    (S : FourSource F torsion hI) (lines : RawAxisLines φ S.a S.b) :
    RepresentativeCoverage φ F torsion lines.kind := by
  let x := ClosureSourceRows.markedKey F torsion hI
  have oneRow : (actualRepresentative F torsion 1).map φ =
      scale (φ (1:L)) (Klein.E lines.kind 1) := by
    rw [actualRepresentative_one,E_one]
    ext u v
    cases u <;> cases v <;> simp [X,Signature.disequality,scale,Matrix.map_apply]
  obtain ⟨cI,hcI,marked⟩ := ClosureSourceRows.representative_marked F torsion hI
  have markedRow : (actualRepresentative F torsion x).map φ =
      scale (φ cI) (Klein.E lines.kind 0) := by
    change (actualRepresentative F torsion (ClosureSourceRows.markedKey F torsion hI)).map φ = _
    rw [marked,mapped_smul,E_zero]
    ext u v
    cases u <;> cases v <;> simp [Matrix.map_apply,Matrix.one_apply,scale]
  have secondRow : (actualRepresentative F torsion S.second).map φ =
      scale (φ lines.leftCoefficient) (Klein.E lines.kind lines.leftIndex) := by
    rw [S.second_raw]
    exact lines.left
  obtain ⟨d,hd,product⟩ := S.product_raw
  have productRow : (actualRepresentative F torsion (x*S.second)).map φ =
      scale (φ (d*lines.rightCoefficient)) (Klein.E lines.kind lines.rightIndex) := by
    change (actualRepresentative F torsion (ClosureSourceRows.markedKey F torsion hI*S.second)).map φ = _
    rw [product,mapped_smul,lines.right]
    exact scale_compose φ d lines.rightCoefficient _
  have productNonzero : d*lines.rightCoefficient ≠ 0 := mul_ne_zero hd lines.rightNonzero
  constructor
  · intro j
    rcases S.keyCases j with h1 | hx | hs | hp
    · subst j
      exact ⟨1,1,one_ne_zero,oneRow⟩
    · subst j
      exact ⟨0,cI,hcI,markedRow⟩
    · subst j
      exact ⟨lines.leftIndex,lines.leftCoefficient,lines.leftNonzero,secondRow⟩
    · subst j
      exact ⟨lines.rightIndex,d*lines.rightCoefficient,productNonzero,productRow⟩
  · rcases lines.indices with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · intro k
      fin_cases k
      · exact ⟨x,cI,hcI,markedRow⟩
      · exact ⟨1,1,one_ne_zero,oneRow⟩
      · exact ⟨S.second,lines.leftCoefficient,lines.leftNonzero,by simpa [hl,Klein.E,Klein.basisQ] using secondRow⟩
      · exact ⟨x*S.second,d*lines.rightCoefficient,productNonzero,by simpa [hr,Klein.E,Klein.basisQ] using productRow⟩
    · intro k
      fin_cases k
      · exact ⟨x,cI,hcI,markedRow⟩
      · exact ⟨1,1,one_ne_zero,oneRow⟩
      · exact ⟨x*S.second,d*lines.rightCoefficient,productNonzero,by simpa [hr,Klein.E,Klein.basisQ] using productRow⟩
      · exact ⟨S.second,lines.leftCoefficient,lines.leftNonzero,by simpa [hl,Klein.E,Klein.basisQ] using secondRow⟩

/-- The source axis and kind are chosen internally from the ACTUAL group.
No caller FourSource, row classifier or coverage certificate is accepted. -/
theorem nativeRepresentativeCoverage (φ : L →+* AlgebraicComplex)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
    (cardinal : Nat.card (completeGroup F torsion) = 4)
    (noncyclic : ¬ IsCyclic (completeGroup F torsion)) :
    ∃ kind : Klein.Kind, RepresentativeCoverage φ F torsion kind := by
  let S := nativeFour F torsion hI cardinal noncyclic
  let lines := ofNativeAxis φ S.a S.b S.nonsingular S.shape
  exact ⟨lines.kind,S.representativeCoverage φ lines⟩

/-- Coverage extends to every ACTUAL source binary, still with original-field
coefficients. This avoids importing a physical/classification source package. -/
theorem nativeActualRows (φ : L →+* AlgebraicComplex)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
    (cardinal : Nat.card (completeGroup F torsion) = 4)
    (noncyclic : ¬ IsCyclic (completeGroup F torsion)) :
    ∃ kind : Klein.Kind,
      (∀ B : Binary (K:=L), ActualNonsingular F B → ∃ k : Fin 4, ∃ c : L, c ≠ 0 ∧
        B.map φ = scale (φ c) (Klein.E kind k)) ∧
      (∀ k : Fin 4, ∃ j : completeGroup F torsion, ∃ c : L, c ≠ 0 ∧
        (actualRepresentative F torsion j).map φ = scale (φ c) (Klein.E kind k)) := by
  obtain ⟨kind,coverage⟩ := nativeRepresentativeCoverage φ F torsion hI cardinal noncyclic
  refine ⟨kind,?_,coverage.backward⟩
  intro B actual
  obtain ⟨j,c,hc,he⟩ := actual_binary_eq_representative F torsion B actual
  obtain ⟨k,d,hd,row⟩ := coverage.forward j
  refine ⟨k,c*d,mul_ne_zero hc hd,?_⟩
  rw [he,mapped_smul,row]
  exact scale_compose φ c d _

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
end
