import Holant.Proofs.Reductions.OriginalFrozenForest.Endpoint
import Holant.Proofs.Reductions.OriginalFrozenForest.StoredTrees
import Holant.Proofs.Reductions.OriginalFrozenForest.QueryReceipts
import Holant.Proofs.Algorithms.OriginalForestSource


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation FrozenFactorNormalization GeneralExtraction
open EdgeSubdivision
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

abbrev K := GeneralOriginalTarget.originalField G
theorem numberField : NumberField (K G) := by
  letI := familyField_finiteDimensional (GeneralOriginalTarget.coefficients G)
    (GeneralOriginalTarget.coefficients_algebraic G)
  exact {to_charZero := inferInstance, to_finiteDimensional := inferInstance}
local instance : NumberField (K G) := numberField G
abbrev embedding : K G →ₐ[ℚ] AlgebraicComplex := (K G).val
abbrev native := OriginalForestSource.nativeSignatures G

theorem native_entry_covered (i : Fin (s+1)) (x : Fin (targetArity s a i.val) → Bool) :
    native G i x ∈ K G := by
  have hm : (⟨targetArity s a i.val,native G i⟩ : AnySignature AlgebraicComplex) ∈
      Set.range (fun j : Fin s => (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)) ∪
        {(⟨2,fun y => Signature.equality (y 0) (y 1)⟩ : AnySignature AlgebraicComplex)} := by
    rw [←Source.native_family G]
    exact ⟨i,rfl⟩
  have covered : ∀ f ∈ Set.range (fun j : Fin s => (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)) ∪
      {(⟨2,fun y => Signature.equality (y 0) (y 1)⟩ : AnySignature AlgebraicComplex)},
      ∀ y, f.2 y ∈ K G := by
    intro f hf
    rcases hf with ⟨j,rfl⟩ | hf
    · intro y
      exact coefficient_mem_familyField (GeneralOriginalTarget.coefficients G) ⟨j,y⟩
    · have he := Set.mem_singleton_iff.mp hf
      subst f
      intro y
      change (if y 0 = y 1 then (1 : AlgebraicComplex) else 0) ∈ K G
      split_ifs
      · exact (K G).one_mem
      · exact (K G).zero_mem
  exact covered _ hm x

def table (i : Fin (s+1)) : Signature (K G) (targetArity s a i.val) :=
  fun x => ⟨native G i x,native_entry_covered G i x⟩
theorem embedded_table : OriginalFrozenForest.embedded (embedding G) (table G)=native G := rfl
def identity : RetainsIdentity (Set.range (fun i =>
    (⟨targetArity s a i.val,OriginalFrozenForest.embedded (embedding G) (table G) i⟩ :
      AnySignature AlgebraicComplex))) := OriginalForestSource.retains_identity G

/-- Exact object equality, including the literal root labels and fixed proofs. -/
theorem same_roots : OriginalFrozenForest.roots (embedding G) (table G) (identity G) =
    OriginalForestSource.roots G := rfl
abbrev D := OriginalForestSource.roots G
abbrev count := OriginalFrozenForest.publicCount (embedding G) (table G) (identity G)
abbrev arity := OriginalFrozenForest.publicArity (embedding G) (table G) (identity G)
abbrev publicTable := OriginalFrozenForest.publicTableL (embedding G) (table G) (identity G)
abbrev family := OriginalFrozenForest.publicFamily (embedding G) (table G) (identity G)
abbrev encoding := OriginalFrozenForest.publicEncoding (embedding G) (table G) (identity G)
abbrev presentation := OriginalLCodec.presentation (L:=K G)
abbrev value := OriginalLCodec.value (publicTable G)

theorem family_exact : Set.range (fun i =>
    (⟨arity G i.val,publicTable G i⟩ : AnySignature (K G))) = family G :=
  OriginalFrozenForest.table_family_exact (embedding G) (table G) (identity G)
/-- Explicit trees for the current normalized alphabet. The root metadata
cast does not call exists_factorTree; all split choices are the saved ones. -/
abbrev storedTrees := OriginalFrozenForest.tableTree (embedding G) (table G) (identity G)
theorem storedTrees_leaves (i : Fin (count G)) (f : AnySignature (K G))
    (hf : f ∈ (storedTrees G i).leaves) : f ∈ family G := by
  rw [←family_exact]
  exact OriginalFrozenForest.tableTree_leaves (embedding G) (table G) (identity G) i f hf

theorem same_catalogue : OriginalFrozenForest.oldTable (embedding G) (table G) (identity G)=
    WholeForest.outputFamily (D G) := rfl
theorem key_descends (i : Fin (RootPreprocessing.count (native G)+WholeForest.count (D G))) :
    RH.mapSignature (embedding G).toRingHom
      (OriginalFrozenForest.storedKey (embedding G) (table G) (identity G) i).table =
      canonicalKey (WholeForest.outputFamily (D G) i) :=
  OriginalFrozenForest.storedKey_exact (embedding G) (table G) (identity G) i
theorem saturated : FactorSaturated (family G) := OriginalFrozenForest.saturated (embedding G) (table G) (identity G)
theorem positive (i : Fin (count G)) : 0 < arity G i.val := by
  change 0 < (PaletteCodec.lookup (embedding G).toRingHom
    (OriginalFrozenForest.literal (embedding G) (table G))
    (OriginalFrozenForest.oldTable (embedding G) (table G) (identity G))
    (OriginalFrozenForest.storedKey (embedding G) (table G) (identity G)) i.val).1
  rw [PaletteCodec.lookup_fin]
  exact OriginalFrozenForest.positive (embedding G) (table G) (identity G) i
theorem nonzero (i : Fin (count G)) : publicTable G i≠0 := by
  change (PaletteCodec.lookup (embedding G).toRingHom
    (OriginalFrozenForest.literal (embedding G) (table G))
    (OriginalFrozenForest.oldTable (embedding G) (table G) (identity G))
    (OriginalFrozenForest.storedKey (embedding G) (table G) (identity G)) i.val).2≠0
  rw [PaletteCodec.lookup_fin]
  exact OriginalFrozenForest.nonzero (embedding G) (table G) (identity G) i
theorem retains_identity : RetainsIdentity (family G) := OriginalFrozenForest.identity (embedding G) (table G) (identity G)
/-- Every preprocessed original tensor is retained LITERALLY after mapping.
The added I is not substituted for an original strict charge witness. -/
theorem retains_preprocessed_original (f : AnySignature AlgebraicComplex)
    (hf : f ∈ Set.range (fun i : Fin s => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex)))
    (hp : 0 < f.1) (hn : f.2≠0) : f ∈ RH.mapFamily (embedding G).toRingHom (family G) := by
  have hm : f ∈ Set.range (fun i : Fin (s+1) =>
      (⟨targetArity s a i.val,native G i⟩ : AnySignature AlgebraicComplex)) := by
    rw [Source.native_family G]
    exact Or.inl hf
  obtain ⟨i,rfl⟩ := hm
  exact ⟨⟨targetArity s a i.val,table G i⟩,
    OriginalFrozenForest.retains_kept (embedding G) (table G) (identity G) i ⟨hp,hn⟩,rfl⟩
theorem degree_bound : Module.finrank ℚ
    (GeneralOriginalTarget.originalField (OriginalFrozenForest.publicTable (embedding G) (table G) (identity G))) ≤
      Module.finrank ℚ (GeneralOriginalTarget.originalField G) :=
  OriginalFrozenForest.degree_bound (embedding G) (table G) (identity G)

/-- Reuse the delivered interpreter with its original-wire terminal already
installed. New controlled adapters are placed BEFORE it; no unrestricted
postcomposition or replacement forest program is introduced. -/
def forestToOriginal : PolyTimeOracleReduction
    (WholeForest.inputEncoding (D G)) (WholeForest.presentation (D G)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (WholeForest.sourceValue (D G)) (OriginalForestSource.value G) :=
  OriginalForestSource.fromForest G

def toOriginal : PolyTimeOracleReduction (encoding G) (presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G) (OriginalForestSource.value G) :=
  (OriginalFrozenForest.publicToCoefficient (embedding G) (table G) (identity G)).compose
    ((OriginalFrozenForest.toCatalogue (embedding G) (table G) (identity G)).compose
      ((OriginalFrozenForest.catalogueToForest (embedding G) (table G) (identity G)).compose (forestToOriginal G)))
def fromOriginal : PolyTimeOracleReduction
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (encoding G) (presentation G).encoding (OriginalForestSource.value G) (value G) :=
  (OriginalWireTransport.literalToNative G).compose
    ((RootPreprocessing.controlled (native G) (OriginalForestSource.retains_identity G)).compose
      ((OriginalCodec.reverse (D G)).compose
        ((OriginalFrozenForest.forestToCatalogue (embedding G) (table G) (identity G)).compose
          ((OriginalFrozenForest.fromCatalogue (embedding G) (table G) (identity G)).compose
            (OriginalFrozenForest.publicFromCoefficient (embedding G) (table G) (identity G)).reduction))))
theorem equivalent :
    OracleReducible (encoding G) (presentation G).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      (value G) (OriginalForestSource.value G) ∧
    OracleReducible (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      (encoding G) (presentation G).encoding (OriginalForestSource.value G) (value G) :=
  ⟨⟨toOriginal G⟩,⟨fromOriginal G⟩⟩

end Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput
