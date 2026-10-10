import Holant.Proofs.Hardness.GeneralEOPairedFamilyBundleOriginal
import Holant.Proofs.Hardness.GeneralEOSignedNativeQuery
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionGadget

/-! Sign variants of a literal gadget are finite signed parent-factor recipes.
Signs cross actual coordinate substitutions; private coordinates and constants
remain explicit in the recipe. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetSigned
open Holant Holant.Tractable
open scoped BigOperators
namespace E
export GeneralEOSignedNativeQuery (count enumeration label signs)
end E
namespace S
export GeneralEOPairedFamilySigned (pairing signed_compressed)
end S
namespace B
export GeneralEOPairedFamilyBundleRaw (Node Recipe)
export GeneralEOPairedFamilyBundleValue (coefficient)
end B
namespace D
export GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end D
namespace T
export GeneralEOPairedFamilyExtractionWriter (tensor)
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

/-- Only the pairing count matters to the ordinary CSP input format. -/
def standard (n : ℕ) : OrientedPerfectPairing (n*2) where
  count := n
  ports := (Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv

def standardFamily (u n : ℕ) : (i : Fin u) → OrientedPerfectPairing ((fun _ : ℕ => n*2) i.val) :=
  fun _ => standard n

def extendSign {m : ℕ} (k : ℕ) (sign : Fin m → Bool) : Fin (m+k) → Bool :=
  Fin.addCases sign (fun _ => false)
def portSign {m k n : ℕ} (sign : Fin m → Bool) (p : Fin n → Bool ⊕ Fin (m+k)) : Fin n → Bool :=
  fun j => Sum.elim (fun _ => false) (extendSign k sign) (p j)
def twist {m : ℕ} (sign z : Fin m → Bool) : Fin m → Bool := fun j => Bool.xor (sign j) (z j)

theorem signed_substitute {m k n : ℕ} (sign : Fin m → Bool)
    (p : Fin n → Bool ⊕ Fin (m+k)) (z : Fin (m+k) → Bool) :
    (fun j => Bool.xor (portSign sign p j) (Sum.elim id z (p j))) =
      T.substitute p (twist (extendSign k sign) z) := by
  funext j
  cases h : p j with
  | inl b => simp [portSign,T.substitute,h]
  | inr i => simp [portSign,T.substitute,h,twist]

theorem twist_add {m k : ℕ} (sign z : Fin m → Bool) (y : Fin k → Bool) :
    twist (extendSign k sign) (Fin.addCases z y) = Fin.addCases (twist sign z) y := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [twist,extendSign]
  · simp [twist,extendSign]

variable {s u m k : ℕ} {arity : ℕ → ℕ}
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

abbrev signedPairing := S.pairing P (E.label P) (E.signs P)

def parentNode (i : Fin s) (sign : Fin m → Bool)
    (p : Fin (P i).count → Bool ⊕ Fin (m+k)) :
    Σ j : Fin (E.count P), Fin (signedPairing P j).count → Bool ⊕ Fin (m+k) :=
  ⟨E.enumeration P ⟨i,portSign sign p⟩,
    fun j => p (Fin.cast
      (congrArg (fun q : GeneralEOSignedNativeQuery.Palette P => (P q.1).count)
        ((E.enumeration P).symm_apply_apply ⟨i,portSign sign p⟩)) j)⟩

variable {K : Type} [Field K]
variable (G : (i : Fin s) → Signature K (arity i.val))

def coefficients (j : Fin (E.count P)) : Signature K (signedPairing P j).count :=
  GeneralEOPairedCSPCycles.compress (signedPairing P j) (GeneralEOPairedFamilyDuplicate.signatures G (E.label P) j)

private theorem palette_value (q a : GeneralEOSignedNativeQuery.Palette P) (h : q=a)
    (z : Fin (P a.1).count → Bool) :
    GeneralEOPairedCSPCycles.compress (P q.1) (G q.1)
      (fun j => Bool.xor (q.2 j) (z (Fin.cast
        (congrArg (fun c : GeneralEOSignedNativeQuery.Palette P => (P c.1).count) h) j))) =
      GeneralEOPairedCSPCycles.compress (P a.1) (G a.1)
        (fun j => Bool.xor (a.2 j) (z j)) := by
  cases h
  rfl

theorem node_value (i : Fin s) (sign : Fin m → Bool)
    (p : Fin (P i).count → Bool ⊕ Fin (m+k)) (z : Fin (m+k) → Bool) :
    coefficients P G (parentNode P i sign p).1
      (fun j => Sum.elim id z ((parentNode P i sign p).2 j)) =
      GeneralEOPairedCSPCycles.compress (P i) (G i)
        (T.substitute p (twist (extendSign k sign) z)) := by
  unfold coefficients
  rw [S.signed_compressed]
  dsimp only [parentNode,signedPairing,GeneralEOPairedFamilySigned.pairing,
    GeneralEOPairedFamilyExtractionOrientation.pairing,GeneralEOPairedFamilySigned.basePairing]
  unfold E.label E.signs
  exact (palette_value P G _ _ ((E.enumeration P).symm_apply_apply ⟨i,portSign sign p⟩)
    (fun j => Sum.elim id z (p j))).trans
      (congrArg (GeneralEOPairedCSPCycles.compress (P i) (G i)) (signed_substitute sign p z))

variable (left right : Fin s)
variable (g : D.Gadget ((P left).count+(P right).count) m)
variable (signs : Fin u → Fin m → Bool)

def leftPort (p : Fin ((P left).count+(P right).count) → Bool ⊕ Fin (m+g.privateCount)) :
    Fin (P left).count → Bool ⊕ Fin (m+g.privateCount) := fun j => p (Fin.castAdd (P right).count j)
def rightPort (p : Fin ((P left).count+(P right).count) → Bool ⊕ Fin (m+g.privateCount)) :
    Fin (P right).count → Bool ⊕ Fin (m+g.privateCount) := fun j => p (Fin.natAdd (P left).count j)

def recipe : B.Recipe (a:=fun _ => (m+g.privateCount)*2) (standardFamily u (m+g.privateCount)) (signedPairing P) :=
  fun i => g.ports.flatMap fun p =>
    [parentNode P left (signs i) (leftPort P left right g p),
     parentNode P right (signs i) (rightPort P left right g p)]

def tensor : Signature K ((P left).count+(P right).count) :=
  T.tensor (GeneralEOPairedCSPCycles.compress (P left) (G left))
    (GeneralEOPairedCSPCycles.compress (P right) (G right))

theorem recipe_value (i : Fin u) (z : Fin (m+g.privateCount) → Bool) :
    B.coefficient (a:=fun _ => (m+g.privateCount)*2) (standardFamily u (m+g.privateCount)) (signedPairing P)
      (recipe P left right g signs) (coefficients P G) i z =
    GeneralEOPairedFamilyExtractionPhaseBundle.evaluate (tensor P G left right) g.ports
      (twist (extendSign g.privateCount (signs i)) z) := by
  unfold B.coefficient recipe GeneralEOPairedFamilyExtractionPhaseBundle.evaluate
  induction g.ports with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,List.prod_append,
      List.prod_cons,List.prod_nil,mul_one]
    rw [node_value,node_value,ih]
    rfl

/-- Summing the fresh private block yields precisely the requested sign variant. -/
theorem private_value (i : Fin u) (z : Fin m → Bool) :
    (∑ y : Fin g.privateCount → Bool,
      B.coefficient (a:=fun _ => (m+g.privateCount)*2) (standardFamily u (m+g.privateCount)) (signedPairing P)
        (recipe P left right g signs) (coefficients P G) i (Fin.addCases z y)) =
      D.denote (tensor P G left right) g (twist (signs i) z) := by
  simp only [recipe_value,twist_add,D.denote]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetSigned
