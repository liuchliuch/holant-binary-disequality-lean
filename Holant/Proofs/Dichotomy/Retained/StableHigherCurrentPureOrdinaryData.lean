import Holant.Proofs.Algorithms.QuaternaryUnaryAccess
import Holant.Proofs.Algorithms.KSourceTransport

/-! The ACTUAL native two-pin palette, embedded by its
coefficient-field inclusion, and the source's fixed normalized K image.
No analytic normalizer is chosen and no matrix is installed as a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open UniversalPairReduction

namespace Pins
export Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess
  (K F paletteArity palette palette_old palette_pin palette_family decoded_exact
   paletteEncoding paletteValue pin pin_nonzero)
end Pins

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
abbrev arity := Pins.paletteArity s a
abbrev inputEncoding := Pins.paletteEncoding s a
abbrev Input := ExactSignatureTables.Input (s+2) 1 (arity (s:=s) (a:=a))

def nativePalette (i : Fin (s+2)) : Signature AlgebraicComplex (arity (s:=s) (a:=a) i.val) :=
  RingHomRealization.mapSignature (Pins.K G).subtype (Pins.palette G i)
def ordinaryPalette := KSourceTransport.ordinarySignatures (nativePalette G)
def unary (b : Bool) : Signature AlgebraicComplex 1 :=
  sourceKBasis.action (Pins.pin (K:=AlgebraicComplex) b)
def pinIndex (b : Bool) : Fin (s+2) := ⟨s+b.toNat,by cases b <;> simp <;> omega⟩
def nativeFamily := Set.range (fun i : Fin (s+2) =>
  (⟨arity (s:=s) (a:=a) i.val,nativePalette G i⟩ : AnySignature AlgebraicComplex))
def ordinaryFamily := Set.range (fun i : Fin (s+2) =>
  (⟨arity (s:=s) (a:=a) i.val,ordinaryPalette G i⟩ : AnySignature AlgebraicComplex))

/-- Whole original family, at the SAME original label indices. -/
theorem native_old (i : Fin s) :
    (⟨arity (s:=s) (a:=a) i.val,nativePalette G ⟨i.val,by have := i.isLt; omega⟩⟩ :
      AnySignature AlgebraicComplex)=⟨a i.val,G i⟩ := by
  calc
    _ = RingHomRealization.mapAny (Pins.K G).subtype
        (⟨Pins.paletteArity s a i.val,Pins.palette G ⟨i.val,by have := i.isLt; omega⟩⟩ :
          AnySignature (Pins.K G)) := rfl
    _ = RingHomRealization.mapAny (Pins.K G).subtype
        (⟨a i.val,QuaternaryUnaryAccess.decoded G i⟩ : AnySignature (Pins.K G)) :=
      congrArg (RingHomRealization.mapAny (Pins.K G).subtype) (Pins.palette_old G i)
    _ = _ := by
      change (⟨a i.val,fun x => (Pins.K G).subtype (QuaternaryUnaryAccess.decoded G i x)⟩ :
        AnySignature AlgebraicComplex) = ⟨a i.val,G i⟩
      exact congrArg (fun f : Signature AlgebraicComplex (a i.val) =>
        (⟨a i.val,f⟩ : AnySignature AlgebraicComplex))
        (funext (fun x => Pins.decoded_exact G i x))

theorem native_pin (b : Bool) :
    (⟨arity (s:=s) (a:=a) (pinIndex (s:=s) b).val,nativePalette G (pinIndex b)⟩ :
      AnySignature AlgebraicComplex)=⟨1,Pins.pin (K:=AlgebraicComplex) b⟩ := by
  have h := congrArg (RingHomRealization.mapAny (Pins.K G).subtype) (Pins.palette_pin G b)
  have hp : RingHomRealization.mapAny (Pins.K G).subtype
      (⟨1,Pins.pin (K:=Pins.K G) b⟩ : AnySignature (Pins.K G))=
        ⟨1,Pins.pin (K:=AlgebraicComplex) b⟩ := by
    change (⟨1,fun x => (Pins.K G).subtype (Pins.pin (K:=Pins.K G) b x)⟩ :
      AnySignature AlgebraicComplex) = ⟨1,Pins.pin b⟩
    exact congrArg (fun f : Signature AlgebraicComplex 1 =>
      (⟨1,f⟩ : AnySignature AlgebraicComplex))
      (by
        funext x
        simp only [QuaternaryUnaryAccess.pin]
        split_ifs <;> simp)
  exact h.trans hp

theorem native_family_exact : nativeFamily G=FiniteFamily.family G ∪
    {(⟨1,Pins.pin (K:=AlgebraicComplex) false⟩ : AnySignature AlgebraicComplex),
      ⟨1,Pins.pin (K:=AlgebraicComplex) true⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<s
    · exact Or.inl ⟨⟨i.val,hi⟩,(native_old G ⟨i.val,hi⟩).symm⟩
    · have hs : i.val=s ∨ i.val=s+1 := by have := i.isLt; omega
      rcases hs with hs|hs
      · have he : i=pinIndex (s:=s) false := Fin.ext (by simpa [pinIndex] using hs)
        rw [he]
        change (⟨arity (s:=s) (a:=a) (pinIndex false).val,
          nativePalette G (pinIndex false)⟩ : AnySignature AlgebraicComplex) ∈ _
        rw [native_pin G false]
        exact Or.inr (by simp)
      · have he : i=pinIndex (s:=s) true := Fin.ext (by simpa [pinIndex] using hs)
        rw [he]
        change (⟨arity (s:=s) (a:=a) (pinIndex true).val,
          nativePalette G (pinIndex true)⟩ : AnySignature AlgebraicComplex) ∈ _
        rw [native_pin G true]
        exact Or.inr (by simp)
  · rintro (⟨i,rfl⟩|h)
    · exact ⟨⟨i.val,by have := i.isLt; omega⟩,native_old G i⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with rfl|rfl
      · exact ⟨pinIndex false,native_pin G false⟩
      · exact ⟨pinIndex true,native_pin G true⟩

theorem ordinary_family_exact : ordinaryFamily G=
    familyAction sourceKBasis (FiniteFamily.family G) ∪
      {(⟨1,unary false⟩ : AnySignature AlgebraicComplex),⟨1,unary true⟩} := by
  have ht : ordinaryFamily G=familyAction sourceKBasis (nativeFamily G) := by
    rw [ordinaryFamily,familyAction,nativeFamily,← Set.range_comp]
    rfl
  rw [ht,native_family_exact,familyAction,Set.image_union,Set.image_insert_eq,Set.image_singleton]
  rfl

theorem ordinary_pin (b : Bool) :
    (⟨arity (s:=s) (a:=a) (pinIndex (s:=s) b).val,ordinaryPalette G (pinIndex b)⟩ :
      AnySignature AlgebraicComplex)=⟨1,unary b⟩ :=
  congrArg (fun f : AnySignature AlgebraicComplex =>
    (⟨f.1,sourceKBasis.action f.2⟩ : AnySignature AlgebraicComplex)) (native_pin G b)

theorem unary_nonzero (b : Bool) : unary b≠0 := by
  intro hz
  have he := congrArg sourceKBasis.symm.action hz
  simp only [unary,InvertibleKernel.symm_action_action] at he
  have hzero : sourceKBasis.symm.action (0 : Signature AlgebraicComplex 1)=0 :=
    Signature.coordinateAction_zero _
  rw [hzero] at he
  exact Pins.pin_nonzero b he

theorem unary_preprocessed (b : Bool) :
    (⟨1,unary b⟩ : AnySignature AlgebraicComplex)∈preprocess (ordinaryFamily G) := by
  refine ⟨⟨pinIndex b,ordinary_pin G b⟩,by change 0 < 1; decide,unary_nonzero b⟩
theorem ordinary_finite : (ordinaryFamily G).Finite := Set.finite_range _
theorem preprocessed_finite : (preprocess (ordinaryFamily G)).Finite :=
  (ordinary_finite G).subset (fun _ h => h.1)

/-- Actual ordinary odd label in the full table. A zero old row or a
nullary old factor is retained by the program; it does not remove this unary. -/
theorem odd_label (b : Bool) :
    Odd (arity (s:=s) (a:=a) (pinIndex (s:=s) b).val) ∧ ordinaryPalette G (pinIndex b)≠0 := by
  have h := ordinary_pin G b
  constructor
  · have ha : arity (s:=s) (a:=a) (pinIndex b).val = 1 := congrArg Sigma.fst h
    rw [ha]
    decide
  · exact Eq.mpr (congrArg (fun f : AnySignature AlgebraicComplex => f.2 ≠ 0) h)
      (unary_nonzero b)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource
