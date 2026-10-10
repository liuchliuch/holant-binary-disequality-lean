import Holant.Proofs.Reductions.FactorSaturation.ForestPowers
import Holant.Proofs.Reductions.FactorSaturation.PrefixMachine
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FactorSaturation.CommonField
open Holant.Tractable
open Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
open GeneralPowerExposure
variable {s : ℕ}
variable (roots : Fin s → AnySignature AlgebraicComplex) (hn : ∀ i, (roots i).2 ≠ 0)
variable (hI : RetainsIdentity (Set.range roots))

def localUnit {f : AnySignature AlgebraicComplex} : FactorTree f → AlgebraicComplexˣ
  | .leaf _ _ => 1
  | .split q _ _ => q.scale

abbrev VertexIndex := Σ i : Fin (s + addedCount roots hn), (Fin (arity roots hn i.val) → Bool)
abbrev Index := VertexIndex roots hn ⊕ (Fin (addedCount roots hn) ⊕ (Node roots hn × Bool))

def coefficient : Index roots hn → AlgebraicComplex
  | .inl ⟨i,x⟩ => (lookup roots hn i.val).2 x
  | .inr (.inl j) => (power roots hn hI j).scale
  | .inr (.inr (u,b)) => if b then (treeScale (node roots hn u).2 : AlgebraicComplex)
      else (localUnit (node roots hn u).2 : AlgebraicComplex)

theorem algebraic (i : Index roots hn) : IsAlgebraic ℚ (coefficient roots hn hI i) :=
  Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (coefficient roots hn hI)
abbrev presentation := familyPresentation (coefficient roots hn hI) (algebraic roots hn hI)

theorem vertex_covered (i : Fin (s + addedCount roots hn)) (x : Fin (arity roots hn i.val) → Bool) :
    (lookup roots hn i.val).2 x ∈ field roots hn hI :=
  coefficient_mem_familyField (coefficient roots hn hI) (.inl ⟨i,x⟩)
theorem macro_scale_covered (j : Fin (addedCount roots hn)) :
    (power roots hn hI j).scale ∈ field roots hn hI :=
  coefficient_mem_familyField (coefficient roots hn hI) (.inr (.inl j))
theorem split_scale_covered (u : Node roots hn) :
    (localUnit (node roots hn u).2 : AlgebraicComplex) ∈ field roots hn hI := by
  simpa [coefficient] using
    coefficient_mem_familyField (coefficient roots hn hI) (.inr (.inr (u,false)))
theorem reconstruction_scale_covered (u : Node roots hn) :
    (treeScale (node roots hn u).2 : AlgebraicComplex) ∈ field roots hn hI := by
  simpa only [coefficient, if_true] using
    coefficient_mem_familyField (coefficient roots hn hI) (.inr (.inr (u,true)))

/-- The out-of-range branch is never a vertex coefficient of the emitted
finite family. It only makes the metadata table total on natural labels. -/
def table (i : ℕ) (x : Fin (arity roots hn i) → Bool) : field roots hn hI :=
  if hi : i < s + addedCount roots hn then
    fieldCoefficient (coefficient roots hn hI) (.inl ⟨⟨i,hi⟩,x⟩) else 0

theorem table_exact (i : ℕ) (hi : i < s + addedCount roots hn) (x : Fin (arity roots hn i) → Bool) :
    (table roots hn hI i x : AlgebraicComplex) = (lookup roots hn i).2 x := by
  simp only [table, dif_pos hi]
  rfl

def scale (j : Fin (addedCount roots hn)) : field roots hn hI :=
  fieldCoefficient (coefficient roots hn hI) (.inr (.inl j))
theorem scale_nonzero (j : Fin (addedCount roots hn)) : scale roots hn hI j ≠ 0 := by
  intro he
  exact (power roots hn hI j).scale_ne_zero (congrArg (fun z : field roots hn hI => (z : AlgebraicComplex)) he)

abbrev smallOriginal := PrefixMachine.family (s:=s) (table roots hn hI) 0
abbrev smallAugmented := PrefixMachine.family (s:=s) (table roots hn hI) (addedCount roots hn)

theorem original_exact (i : Fin s) (x : Fin (arity roots hn i.val) → Bool) :
    (smallOriginal roots hn hI i x : AlgebraicComplex) = original roots hn i x :=
  table_exact roots hn hI i.val (by have := i.isLt; omega) x

/-- Lift the SAME actual labelled graph, with its local tensor identity
proved through the faithful field inclusion; no new macro premise is added. -/
def «macro» (j : Fin (addedCount roots hn)) :
    PowerMacro (smallOriginal roots hn hI) (table roots hn hI (s+j.val)) where
  exponent := (power roots hn hI j).exponent
  positive := (power roots hn hI j).positive
  scale := scale roots hn hI j
  scale_ne_zero := scale_nonzero roots hn hI j
  network := (power roots hn hI j).labels.sourceNetwork (smallOriginal roots hn hI)
    (fun _ => Signature.disequality)
  labels := (power roots hn hI j).labels
  value := by
    let P := power roots hn hI j
    let M := P.labels.template.network P.labels.wellFormed (smallOriginal roots hn hI)
      (fun _ : Fin 1 => Signature.disequality)
    have he : M.map (field roots hn hI).subtype =
        P.labels.template.network P.labels.wellFormed (original roots hn) (fun _ => Signature.disequality) := by
      unfold M Network.map Template.network
      congr 1
      · funext v x
        exact original_exact roots hn hI _ _
      · funext e a b
        cases a <;> cases b <;> rfl
    funext x
    apply Subtype.ext
    change (field roots hn hI).subtype (M.denote x) = _
    rw [← Network.denote_map, he, P.value]
    simp only [Carrier.blockPower, map_mul, map_prod]
    congr 1
    change _ = (field roots hn hI).subtype _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact (table_exact roots hn hI (s+j.val) (by have := j.isLt; omega) _).symm

theorem original_field_le : GeneralOriginalTarget.originalField (original roots hn) ≤ field roots hn hI := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  exact vertex_covered roots hn hI ⟨i.val,by have := i.isLt; omega⟩ x

def embedding : GeneralOriginalTarget.originalField (original roots hn) →ₐ[ℚ] field roots hn hI :=
  IntermediateField.inclusion (original_field_le roots hn hI)

theorem mapped_tables :
    Holant.LocalDrafts.MainChain.TableFieldTransport.mapTables
      (GeneralOriginalTarget.originalPresentation (original roots hn)) (presentation roots hn hI)
      (embedding roots hn hI) (GeneralOriginalTarget.originalTables (original roots hn)) =
      GeneralFieldReduction.targetTables (presentation roots hn hI) (smallOriginal roots hn hI) := by
  unfold Holant.LocalDrafts.MainChain.TableFieldTransport.mapTables GeneralOriginalTarget.originalTables
    GeneralFieldReduction.targetTables Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    exact (original_exact roots hn hI i x).symm
  · funext i a b
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases a <;> cases b <;> simp [Signature.disequality]

def originalTransport : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 (arity roots hn)) (presentation roots hn hI).encoding
    (RawClosedNetwork.validatedEncoding s 1 (arity roots hn))
      (GeneralOriginalTarget.originalPresentation (original roots hn)).encoding
    ((GeneralFieldReduction.targetTables (presentation roots hn hI) (smallOriginal roots hn hI)).evaluate
      (presentation roots hn hI)) (GeneralOriginalTarget.originalValue (original roots hn)) := by
  have R := Holant.LocalDrafts.MainChain.TableFieldTransport.toOriginal
    (GeneralOriginalTarget.originalPresentation (original roots hn)) (presentation roots hn hI)
    (embedding roots hn hI) (GeneralOriginalTarget.originalTables (original roots hn))
  rw [mapped_tables roots hn hI] at R
  exact R

end Holant.LocalDrafts.Hardness.FactorSaturation.CommonField
