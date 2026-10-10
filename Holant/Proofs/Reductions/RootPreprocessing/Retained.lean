import Holant.Proofs.Reductions.FactorSaturation.OriginalCodec
import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Proofs.Algorithms.RawArityTransport


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def Keep (i : Fin s) : Prop := 0 < a i.val ∧ G i ≠ 0
def retained : Finset (Fin s) := Finset.univ.filter (Keep G)
@[simp] theorem mem_retained (i : Fin s) : i ∈ retained G ↔ Keep G i := by
  simp [retained]
abbrev Label := {i : Fin s // i ∈ retained G}
abbrev count := Fintype.card (Label G)
def enumeration : Fin (count G) ≃ Label G := (Fintype.equivFin (Label G)).symm
def includeLabel (j : Fin (count G)) : Fin s := (enumeration G j).val
def compact (i : Fin s) (hi : Keep G i) : Fin (count G) :=
  (enumeration G).symm ⟨i,(mem_retained G i).mpr hi⟩

@[simp] theorem include_compact (i : Fin s) (hi : Keep G i) :
    includeLabel G (compact G i hi) = i := by simp [includeLabel,compact]
@[simp] theorem compact_include (j : Fin (count G))
    (h : Keep G (includeLabel G j)) : compact G (includeLabel G j) h = j := by
  apply (enumeration G).injective
  apply Subtype.ext
  simp [compact,includeLabel]
theorem included_kept (j : Fin (count G)) : Keep G (includeLabel G j) :=
  (mem_retained G _).mp (enumeration G j).property

def signature (j : Fin (count G)) : AnySignature AlgebraicComplex :=
  ⟨a (includeLabel G j).val,G (includeLabel G j)⟩
abbrev targetArity := OriginalCodec.rootArity (signature G)
abbrev targetTable := OriginalCodec.rootTable (signature G)
@[simp] theorem target_arity (j : Fin (count G)) :
    targetArity G j.val = a (includeLabel G j).val := by
  simp [targetArity,OriginalCodec.rootArity,signature]

theorem identity_nonzero :
    Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature
      (K := AlgebraicComplex) ≠ 0 := by
  intro h
  have hz := congrFun h (fun _ => false)
  simpa [Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,
    Signature.equality] using hz

variable (hI : RetainsIdentity
  (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))

include hI in
theorem retained_identity : RetainsIdentity (Set.range (signature G)) := by
  obtain ⟨i,hi⟩ := hI
  dsimp only at hi
  have hk : Keep G i := by
    have hp : 0 < (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex).1 :=
      (congrArg (fun f : AnySignature AlgebraicComplex => 0 < f.1) hi).mpr (by decide)
    have hn : (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex).2 ≠ 0 :=
      (congrArg (fun f : AnySignature AlgebraicComplex => f.2 ≠ 0) hi).mpr identity_nonzero
    exact ⟨hp,hn⟩
  refine ⟨compact G i hk,?_⟩
  exact (congrArg (fun j : Fin s => (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex))
    (include_compact G i hk)).trans hi

/-- The old forest boundary is constructed, not assumed. -/
def roots : WholeForest.Roots (count G) where
  signature := signature G
  nonzero j := (included_kept G j).2
  positive j := (included_kept G j).1
  identity := retained_identity G hI

theorem retained_exact : Set.range (signature G) =
    {f | ∃ i : Fin s, Keep G i ∧ f = ⟨a i.val,G i⟩} := by
  ext f
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨includeLabel G j,included_kept G j,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨compact G i hi,congrArg (fun j : Fin s =>
      (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)) (include_compact G i hi)⟩

abbrev Input := ExactSignatureTables.Input s 1 a
abbrev sourceEncoding := RawClosedNetwork.validatedEncoding s 1 a
def nativeX : Fin 1 → Kernel AlgebraicComplex := fun _ => Signature.disequality
abbrev sourceCoefficient := Holant.LocalDrafts.MainChain.OriginalFamily.coefficient G nativeX
abbrev sourceField := familyField (sourceCoefficient G)
abbrev sourcePresentation := Holant.LocalDrafts.MainChain.OriginalFamily.presentation G nativeX
abbrev sourceTables := Holant.LocalDrafts.MainChain.OriginalFamily.tables G nativeX
abbrev sourceValue := Holant.LocalDrafts.MainChain.OriginalFamily.value G nativeX

end Holant.LocalDrafts.Hardness.RootPreprocessing
