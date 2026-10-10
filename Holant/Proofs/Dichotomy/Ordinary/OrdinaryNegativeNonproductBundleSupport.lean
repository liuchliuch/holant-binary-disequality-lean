import Holant.Proofs.Reductions.EightVertexNonexception.SparseExclusions
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSubstitution

/-! Product-square support extraction for an arbitrary literal ordinary row.
The coordinate gauge below is semantic only; every original coordinate and its
sign are retained by the resulting two-bundle descriptor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleSupport
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute product_substitute)
end T
namespace S
export GeneralEOPairedFamilyExtractionSupport (origin xor meet XorClosed MeetClosed product_meetClosed)
end S
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull
  (expand reduced expand_fixed expand_substitute substitution reduced_full product_of_reduced)
end C
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose facePorts face_substitute substitute_compose)
end I
namespace B
export EOBinaryPlaneClassification (Full Cross full_product_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {m n : ℕ}

def flip (s x : Fin n → Bool) : Fin n → Bool := fun i => s i ^^ x i

@[simp] theorem flip_flip (s x : Fin n → Bool) : flip s (flip s x)=x := by
  funext i
  simp [flip]

@[simp] theorem flip_origin (s : Fin n → Bool) : flip s S.origin=s := by
  funext i
  simp [flip,S.origin]

def shifted (f : Signature AlgebraicComplex n) (s : Fin n → Bool) :
    Signature AlgebraicComplex n := fun x => f (flip s x)

theorem product_flip (s : Fin n → Bool) {f : Signature AlgebraicComplex n}
    (hp : Product f) : Product (shifted f s) := by
  have factor (p : ProductFactor n) : Product (shifted p.eval s) := by
    cases p with
    | unary i u hu => exact product_unary i (fun b => u (s i ^^ b))
    | equality i j =>
        by_cases h : s i=s j
        · convert product_equality i j using 1
          funext x
          cases hsi : s i <;> cases hxi : x i <;> cases hxj : x j <;>
            simp [shifted,flip,ProductFactor.eval,Signature.equality,←h,hsi,hxi,hxj]
        · convert product_disequality i j using 1
          funext x
          cases hsi : s i <;> cases hsj : s j <;> cases hxi : x i <;> cases hxj : x j <;>
            simp_all [shifted,flip,ProductFactor.eval,Signature.equality,Signature.disequality]
    | disequality i j =>
        by_cases h : s i=s j
        · convert product_disequality i j using 1
          funext x
          cases hsi : s i <;> cases hxi : x i <;> cases hxj : x j <;>
            simp [shifted,flip,ProductFactor.eval,Signature.disequality,←h,hsi,hxi,hxj]
        · convert product_equality i j using 1
          funext x
          cases hsi : s i <;> cases hsj : s j <;> cases hxi : x i <;> cases hxj : x j <;>
            simp_all [shifted,flip,ProductFactor.eval,Signature.equality,Signature.disequality]
  have factors (ps : List (ProductFactor n)) :
      Product (fun x => (ps.map (fun p => p.eval (flip s x))).prod) := by
    induction ps with
    | nil => exact product_constant n 1
    | cons p ps ih => exact (factor p).mul ih
  rcases hp with rfl | ⟨c,hc,ps,rfl⟩
  · exact product_zero n
  · exact (factors ps).scale c

theorem product_shifted_iff (s : Fin n → Bool) (f : Signature AlgebraicComplex n) :
    Product (shifted f s) ↔ Product f := by
  refine ⟨fun h => ?_,product_flip s⟩
  have h' := product_flip s h
  change Product (fun x => f (flip s (flip s x))) at h'
  simpa only [flip_flip] using h'

def signedWord (s : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin m → Bool) : Fin n → Bool := flip s (T.substitute p z)

/-- Class reflection uses signed coordinate substitution only as a semantic
lemma. It does not make a compressed row physically available. -/
theorem product_signed_substitute (s : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    {f : Signature AlgebraicComplex n} (hp : Product f) :
    Product (fun z => f (signedWord s p z)) :=
  T.product_substitute p (product_flip s hp)

theorem square_support (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    f x^2≠0 ↔ f x≠0 := pow_ne_zero_iff (by decide)

theorem square_closed (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hp : Product (fun x => f x^2)) : S.XorClosed f ∧ S.MeetClosed f := by
  constructor
  · intro u v hu hv
    have hh := product_support_xor3 hp u v S.origin
      (pow_ne_zero 2 hu) (pow_ne_zero 2 hv) (pow_ne_zero 2 h0)
    apply (square_support f _).mp
    convert hh using 1
    congr 2
    funext i
    simp [xor3,S.origin,S.xor]
  · intro u v hu hv
    exact (square_support f _).mp (S.product_meetClosed _ (pow_ne_zero 2 h0) hp
      u v (pow_ne_zero 2 hu) (pow_ne_zero 2 hv))

/-- The signed two-bundle descriptor is chosen from the original row. Its
binary witness has full support and nonzero determinant, while its square is
Product. The original gauge and every original port remain explicit. -/
structure Face (f : Signature AlgebraicComplex n) where
  base : Fin n → Bool
  base_nonzero : f base≠0
  first : Fin n
  second : Fin n
  distinct : first≠second
  fixed : Fin n → Bool
  full : B.Full (fun z => f (signedWord base
    (I.compose (C.substitution (shifted f base)) (I.facePorts first second fixed)) z))
  nonproduct : ¬Product (fun z => f (signedWord base
    (I.compose (C.substitution (shifted f base)) (I.facePorts first second fixed)) z))
  square : Product (fun z => (f (signedWord base
    (I.compose (C.substitution (shifted f base)) (I.facePorts first second fixed)) z))^2)

namespace Face
variable {f : Signature AlgebraicComplex n}

def ports (D : Face f) : Fin n → Bool ⊕ Fin 2 :=
  I.compose (C.substitution (shifted f D.base)) (I.facePorts D.first D.second D.fixed)

def binary (D : Face f) : Signature AlgebraicComplex 2 := fun z => f (signedWord D.base D.ports z)

theorem determinant_nonzero (D : Face f) :
    D.binary ![false,false]*D.binary ![true,true]-
      D.binary ![false,true]*D.binary ![true,false]≠0 := by
  intro hz
  exact D.nonproduct ((B.full_product_iff _ D.full).mpr (sub_eq_zero.mp hz))

end Face

/-- Arbitrary arity and arbitrary support, including fixed components and
arbitrary signed bundle sizes. No support partition is a caller premise. -/
theorem exists_face (f : Signature AlgebraicComplex n) (hn : ¬Product f)
    (hs : Product (fun x => f x^2)) : Nonempty (Face f) := by
  classical
  have nonzero : f≠0 := fun h => hn (Or.inl h)
  obtain ⟨s,hs0⟩ := Function.ne_iff.mp nonzero
  change f s≠0 at hs0
  let g := shifted f s
  have h0 : g S.origin≠0 := by simpa only [g,shifted,flip_origin] using hs0
  have hg : ¬Product g := fun h => hn ((product_shifted_iff s f).mp h)
  have hsq : Product (fun x => g x^2) := product_flip s hs
  obtain ⟨hx,hm⟩ := square_closed g h0 hsq
  obtain ⟨i,j,hij,x,hfull,hprod⟩ :=
    GeneralEOPairedFamilyExtractionComponentsFull.exists_nonproduct_face g h0 hx hm hg
  let p := I.compose (C.substitution g) (I.facePorts i j x)
  have equation : (fun z => f (signedWord s p z))=
      GeneralEOPairedFamilyExtractionFullSupport.face (C.reduced g) i j x := by
    funext z
    change g (T.substitute p z)=_
    rw [show p=I.compose (C.substitution g) (I.facePorts i j x) from rfl,
      I.substitute_compose,←C.expand_substitute]
    exact I.face_substitute (C.reduced g) i j x z
  refine ⟨⟨s,hs0,i,j,hij,x,?_,?_,product_signed_substitute s p hs⟩⟩
  · change B.Full (fun z => f (signedWord s p z))
    rwa [equation]
  · change ¬Product (fun z => f (signedWord s p z))
    rwa [equation]

def extract (f : Signature AlgebraicComplex n) (hn : ¬Product f)
    (hs : Product (fun x => f x^2)) : Face f :=
  Classical.choice (exists_face f hn hs)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleSupport
end
