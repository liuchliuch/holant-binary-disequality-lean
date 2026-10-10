import Holant.Proofs.Reductions.OriginalFrozenForest.Palette


noncomputable section
namespace Holant.LocalDrafts.Hardness.OriginalFrozenForest
open Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L] (φ : L →ₐ[ℚ] AlgebraicComplex)
variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature L (a i.val))
variable (hI : RetainsIdentity (Set.range (fun i =>
  (⟨a i.val,embedded φ G i⟩ : AnySignature AlgebraicComplex))))

include hI in
theorem literal_nonzero (i : Fin (rootCount φ G)) : (literal φ G i).2≠0 := by
  intro hz
  apply (roots φ G hI).nonzero i
  change RH.mapSignature φ.toRingHom (literal φ G i).2 = 0
  funext x
  simp [RH.mapAny,RH.mapSignature,hz]

def literalPivot (i : Fin (rootCount φ G)) : Lˣ :=
  Units.mk0 ((literal φ G i).2 (firstWord (literal φ G i).2 (literal_nonzero φ G hI i)))
    (firstWord_nonzero _ (literal_nonzero φ G hI i))
theorem literal_key (i : Fin (rootCount φ G)) :
    lifted φ.toRingHom (storedKey φ G hI (rootToOld φ G hI i)) =
      ⟨(literal φ G i).1,canonicalKey (literal φ G i).2⟩ := by
  apply mapAny_injective φ.toRingHom
  rw [lifted_map,←literal_old φ G hI i]
  exact (congrArg (fun t => (⟨(literal φ G i).1,t⟩ : AnySignature AlgebraicComplex))
    (key_map φ.toRingHom (literal φ G i).2)).symm
theorem literal_restore (i : Fin (rootCount φ G)) :
    scaled (literalPivot φ G hI i)
      (lifted φ.toRingHom (storedKey φ G hI (rootToOld φ G hI i))) = literal φ G i := by
  rw [literal_key]
  exact congrArg (fun t => (⟨(literal φ G i).1,t⟩ : AnySignature L))
    (recover_from_key (literal φ G i).2 (literal_nonzero φ G hI i)).symm

def keyTree (i : Fin (oldCount φ G hI)) :
    FactorTree (lifted φ.toRingHom (storedKey φ G hI i)) :=
  normalizedTree φ.toRingHom (actualTree φ G hI i) (old_nonzero φ G hI i) (storedKey φ G hI i)
theorem keyTree_leaf_receipt (i : Fin (oldCount φ G hI)) (u : AnySignature L)
    (hu : u ∈ (keyTree φ G hI i).leaves) :
    ∃ v ∈ (actualTree φ G hI i).leaves, RH.mapAny φ.toRingHom u = keyAny v :=
  normalizedTree_leaves φ.toRingHom (actualTree φ G hI i) (old_nonzero φ G hI i)
    (storedKey φ G hI i) u hu
theorem keyTree_leaves (i : Fin (oldCount φ G hI)) (u : AnySignature L)
    (hu : u ∈ (keyTree φ G hI i).leaves) : u ∈ publicFamily φ G hI :=
  Palette.normalized_leaves φ.toRingHom (literal φ G) (oldAny φ G hI) (storedKey φ G hI)
    (old_nonzero φ G hI) (actualTree φ G hI) (actualTree_leaves φ G hI) i u hu

def literalTree (i : Fin (rootCount φ G)) : FactorTree (literal φ G i) :=
  transportTree (literal_restore φ G hI i)
    (scaleTree (keyTree φ G hI (rootToOld φ G hI i)) (literalPivot φ G hI i))
theorem literalTree_leaves (i : Fin (rootCount φ G)) (u : AnySignature L)
    (hu : u ∈ (literalTree φ G hI i).leaves) : u ∈ publicFamily φ G hI := by
  rw [literalTree,transportTree_leaves] at hu
  rcases scaleTree_leaves _ (literalPivot φ G hI i) u hu with he | hk
  · rw [he,literal_restore]
    exact Palette.retains_root φ.toRingHom _ _ _ i
  · exact keyTree_leaves φ G hI _ u hk

def publicTree (i : Fin (publicCount φ G hI)) : FactorTree (publicSignature φ G hI i) :=
  if hi : i.val < rootCount φ G then
    transportTree (show literal φ G ⟨i.val,hi⟩ = publicSignature φ G hI i by
      simp only [publicSignature,Palette.signature,dif_pos hi]) (literalTree φ G hI ⟨i.val,hi⟩)
  else
    transportTree (show lifted φ.toRingHom (storedKey φ G hI ⟨i.val-rootCount φ G,by
          have hb : i.val < rootCount φ G + oldCount φ G hI := i.isLt
          omega⟩) =
        publicSignature φ G hI i by
      simp only [publicSignature,Palette.signature,dif_neg hi])
      (keyTree φ G hI ⟨i.val-rootCount φ G,by
          have hb : i.val < rootCount φ G + oldCount φ G hI := i.isLt
          omega⟩)
theorem publicTree_leaves (i : Fin (publicCount φ G hI)) (u : AnySignature L)
    (hu : u ∈ (publicTree φ G hI i).leaves) : u ∈ publicFamily φ G hI := by
  by_cases hi : i.val < rootCount φ G
  · simp only [publicTree,dif_pos hi,transportTree_leaves] at hu
    exact literalTree_leaves φ G hI _ u hu
  · simp only [publicTree,dif_neg hi,transportTree_leaves] at hu
    exact keyTree_leaves φ G hI _ u hu

theorem public_table_literal (i : Fin (publicCount φ G hI)) :
    (⟨publicArity φ G hI i.val,publicTableL φ G hI i⟩ : AnySignature L) = publicSignature φ G hI i :=
  PaletteCodec.lookup_fin φ.toRingHom (literal φ G) (oldTable φ G hI) (storedKey φ G hI) i
theorem table_family_exact : Set.range (fun i =>
    (⟨publicArity φ G hI i.val,publicTableL φ G hI i⟩ : AnySignature L)) = publicFamily φ G hI := by
  change Set.range (fun i => (⟨publicArity φ G hI i.val,publicTableL φ G hI i⟩ : AnySignature L)) =
    Set.range (publicSignature φ G hI)
  exact congrArg Set.range (funext (public_table_literal φ G hI))

/-- A metadata cast of the saved normalized occurrence, not a new tree choice. -/
def tableTree (i : Fin (publicCount φ G hI)) :
    FactorTree (⟨publicArity φ G hI i.val,publicTableL φ G hI i⟩ : AnySignature L) :=
  transportTree (public_table_literal φ G hI i).symm (publicTree φ G hI i)
theorem tableTree_leaves (i : Fin (publicCount φ G hI)) (u : AnySignature L)
    (hu : u ∈ (tableTree φ G hI i).leaves) :
    u ∈ Set.range (fun j => (⟨publicArity φ G hI j.val,publicTableL φ G hI j⟩ : AnySignature L)) := by
  rw [table_family_exact]
  rw [tableTree,transportTree_leaves] at hu
  exact publicTree_leaves φ G hI i u hu

end Holant.LocalDrafts.Hardness.OriginalFrozenForest
