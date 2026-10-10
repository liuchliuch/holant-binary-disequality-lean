import Holant.Proofs.Reductions.CanonicalFamily.NormalForm


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def key (i : Fin s) : AnySignature AlgebraicComplex := ⟨a i.val,canonicalKey (G i)⟩
def fiber (i : Fin s) : Finset (Fin s) := Finset.univ.filter (fun j => key G j = key G i)
theorem fiber_nonempty (i : Fin s) : (fiber G i).Nonempty := ⟨i,by simp [fiber]⟩
def representative (i : Fin s) : Fin s := (fiber G i).min' (fiber_nonempty G i)
theorem representative_key (i : Fin s) : key G (representative G i) = key G i := by
  have h := Finset.min'_mem (fiber G i) (fiber_nonempty G i)
  simpa [fiber,representative] using h
theorem representative_le (i j : Fin s) (h : key G j = key G i) : representative G i ≤ j :=
  Finset.min'_le _ _ (by simp [fiber,h])
theorem representative_eq (i j : Fin s) (h : key G i = key G j) :
    representative G i = representative G j := by
  apply le_antisymm
  · exact representative_le G i _ ((representative_key G j).trans h.symm)
  · exact representative_le G j _ ((representative_key G i).trans h)
@[simp] theorem representative_idempotent (i : Fin s) :
    representative G (representative G i) = representative G i :=
  representative_eq G _ i (representative_key G i)

def representatives : Finset (Fin s) := Finset.univ.image (representative G)
abbrev count := (representatives G).card
def enumeration : Fin (count G) ≃o {i : Fin s // i ∈ representatives G} :=
  (representatives G).orderIsoOfFin rfl
def selected (j : Fin (count G)) : Fin s := (enumeration G j).val
theorem representative_mem (i : Fin s) : representative G i ∈ representatives G := by
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
theorem selected_fixed (j : Fin (count G)) : representative G (selected G j) = selected G j := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (enumeration G j).property
  change representative G ((enumeration G j).val) = (enumeration G j).val
  rw [← hi,representative_idempotent]

def toKey (i : Fin s) : Fin (count G) :=
  (enumeration G).symm ⟨representative G i,representative_mem G i⟩
@[simp] theorem selected_toKey (i : Fin s) : selected G (toKey G i) = representative G i := by
  simp [selected,toKey]
@[simp] theorem toKey_selected (j : Fin (count G)) : toKey G (selected G j) = j := by
  apply (enumeration G).injective
  apply Subtype.ext
  simp only [toKey,OrderIso.apply_symm_apply]
  exact selected_fixed G j
def signature (j : Fin (count G)) : AnySignature AlgebraicComplex := key G (selected G j)
@[simp] theorem signature_toKey (i : Fin s) : signature G (toKey G i) = key G i := by
  simp [signature,representative_key]
theorem signature_injective : Function.Injective (signature G) := by
  intro i j h
  have hr := representative_eq G (selected G i) (selected G j) h
  have he : selected G i = selected G j := by simpa only [selected_fixed] using hr
  exact (enumeration G).injective (Subtype.ext he)
theorem label_eq_iff (i j : Fin s) : toKey G i = toKey G j ↔ key G i = key G j := by
  constructor
  · intro h
    simpa using congrArg (signature G) h
  · intro h
    apply (enumeration G).injective
    apply Subtype.ext
    simpa [toKey] using representative_eq G i j h
theorem exact_range : Set.range (signature G) = Set.range (key G) := by
  ext f
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨selected G j,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨toKey G i,signature_toKey G i⟩

abbrev arity := OriginalCodec.rootArity (signature G)
abbrev table := OriginalCodec.rootTable (signature G)
theorem table_signature (j : Fin (count G)) :
    (⟨arity G j.val,table G j⟩ : AnySignature AlgebraicComplex) = signature G j :=
  OriginalCodec.rootLookup_old (signature G) j
theorem table_injective : Function.Injective
    (fun j => (⟨arity G j.val,table G j⟩ : AnySignature AlgebraicComplex)) := by
  intro i j h
  apply signature_injective G
  simpa only [table_signature] using h
@[simp] theorem arity_selected (j : Fin (count G)) : arity G j.val = a (selected G j).val := by
  simp [arity,OriginalCodec.rootArity,signature,key]
theorem arity_toKey (i : Fin s) : arity G (toKey G i).val = a i.val := by
  change (OriginalCodec.rootLookup (signature G) (toKey G i).val).1 = _
  rw [OriginalCodec.rootLookup_old,signature_toKey] <;> rfl

variable (hn : ∀ i, G i ≠ 0)
def pivot (i : Fin s) : AlgebraicComplex := G i (firstWord (G i) (hn i))
theorem pivot_nonzero (i : Fin s) : pivot G hn i ≠ 0 := firstWord_nonzero (G i) (hn i)
theorem recover (i : Fin s) : G i = pivot G hn i • canonicalKey (G i) := recover_from_key (G i) (hn i)
theorem reverse_scale (j : Fin (count G)) : canonicalKey (G (selected G j)) =
    (pivot G hn (selected G j))⁻¹ • G (selected G j) :=
  canonicalKey_of_ne_zero _ (hn _)
theorem normalized (j : Fin (count G)) :
    canonicalKey (signature G j).2 = (signature G j).2 := key_idempotent _
include hn in
theorem nonzero (j : Fin (count G)) : (signature G j).2 ≠ 0 := canonicalKey_nonzero _ (hn _)
theorem first_entry (j : Fin (count G)) :
    (signature G j).2 (firstWord (signature G j).2 (nonzero G hn j)) = 1 :=
  normalized_first_entry _ (hn _)

variable (hp : ∀ i : Fin s, 0 < a i.val)
variable (hI : RetainsIdentity (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))
theorem identity_label (i : Fin s)
    (hi : (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex) = ⟨2,literalI⟩) :
    signature G (toKey G i) = (⟨2,literalI⟩ : AnySignature AlgebraicComplex) := by
  rw [signature_toKey]
  have h := congrArg (fun f : AnySignature AlgebraicComplex =>
    (⟨f.1,canonicalKey f.2⟩ : AnySignature AlgebraicComplex)) hi
  simpa [key,identity_key] using h
include hI in
theorem retains_identity : RetainsIdentity (Set.range (signature G)) := by
  obtain ⟨i,hi⟩ := hI
  exact ⟨toKey G i,identity_label G i hi⟩
def roots : WholeForest.Roots (count G) where
  signature := signature G
  nonzero := nonzero G hn
  positive j := hp (selected G j)
  identity := retains_identity G hI

end Holant.LocalDrafts.Hardness.CanonicalFamily
