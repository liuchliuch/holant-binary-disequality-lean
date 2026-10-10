import Holant.Proofs.Hardness.GeneralEONegativeTensorCore

/-! MWX, arXiv:2502.02012v2, Lemma 54: the two incompatible strict support
signs are reduced to a single central missing triple xor by an actual tensor
union. Multiplicities are the opposite witness charges, not assumed gadget
parameters. The construction works for arbitrary original arities and values.
This is a support reduction, not an imported hardness theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeSupportTensor
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace C
export GeneralEONegativeTensorCore
  (arity graph word readWord charge_word triple_word supported_word missing_word central
    labelling template valid template_denote arity_sum)
end C
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

structure Triple (f : Signature K n) where
  first : Fin n → Bool
  second : Fin n → Bool
  third : Fin n → Bool
  first_supported : f first≠0
  second_supported : f second≠0
  third_supported : f third≠0

def Triple.xor {f : Signature K n} (T : Triple f) := tripleXor T.first T.second T.third

def CentralHole (f : Signature K n) : Prop :=
  ∃T : Triple f,f T.xor=0 ∧ charge T.xor=0

theorem centralHole_not_supports {f : Signature AlgebraicComplex n}
    (h : CentralHole f) (sign : EOSign) : ¬EONegativeWitness.Supports sign ⟨n,f⟩ := by
  obtain ⟨T,hz,hc⟩ := h
  intro hs
  rcases hs T.first T.second T.third T.first_supported T.second_supported T.third_supported with hs|hs
  · exact hs hz
  · change 0<sign.value*charge T.xor at hs
    rw [hc,mul_zero] at hs
    omega

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (i j : Fin s) (r u : ℕ)

abbrev labels (v : Fin (r+u)) : Fin s := if v.val<r then i else j

private def transportWord {k l : Fin s} (h : k=l) (x : Fin (a l.val)→Bool) : Fin (a k.val)→Bool :=
  cast (congrArg (fun q : Fin s=>Fin (a q.val)→Bool) h.symm) x

private theorem charge_transport {k l : Fin s} (h : k=l) (x : Fin (a l.val)→Bool) :
    charge (transportWord h x)=charge x := by cases h; rfl

private theorem value_transport {k l : Fin s} (h : k=l) (x : Fin (a l.val)→Bool) :
    G k (transportWord h x)=G l x := by cases h; rfl

private theorem triple_transport {k l : Fin s} (h : k=l) (x y z : Fin (a l.val)→Bool) :
    tripleXor (transportWord h x) (transportWord h y) (transportWord h z)=
      transportWord h (tripleXor x y z) := by cases h; rfl

def words (x : Fin (a i.val) → Bool) (y : Fin (a j.val) → Bool)
    (v : Fin (r+u)) : Fin (a (labels i j r u v).val)→Bool :=
  if h : v.val<r then transportWord (show labels i j r u v=i from if_pos h) x
  else transportWord (show labels i j r u v=j from if_neg h) y

private theorem words_charge (x : Fin (a i.val)→Bool) (y : Fin (a j.val)→Bool)
    (v : Fin (r+u)) : charge (words i j r u x y v)=
      if v.val<r then charge x else charge y := by
  unfold words
  split_ifs <;> apply charge_transport

private theorem words_value (x : Fin (a i.val)→Bool) (y : Fin (a j.val)→Bool)
    (v : Fin (r+u)) : G (labels i j r u v) (words i j r u x y v)=
      if v.val<r then G i x else G j y := by
  unfold words
  split_ifs <;> apply value_transport

def combinedWord (x : Fin (a i.val) → Bool) (y : Fin (a j.val) → Bool) :=
  C.word (labels i j r u) (words i j r u x y)

abbrev combined := C.graph (a:=a) (labels i j r u) G

theorem combined_charge (x : Fin (a i.val) → Bool) (y : Fin (a j.val) → Bool) :
    charge (combinedWord i j r u x y)=(r:ℤ)*charge x+(u:ℤ)*charge y := by
  rw [combinedWord,C.charge_word]
  simp only [words_charge,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd]
  simp

theorem combined_xor (x₁ x₂ x₃ : Fin (a i.val) → Bool)
    (y₁ y₂ y₃ : Fin (a j.val) → Bool) :
    tripleXor (combinedWord i j r u x₁ y₁) (combinedWord i j r u x₂ y₂)
      (combinedWord i j r u x₃ y₃)=
      combinedWord i j r u (tripleXor x₁ x₂ x₃) (tripleXor y₁ y₂ y₃) := by
  rw [combinedWord,combinedWord,combinedWord,C.triple_word]
  congr 1
  funext v
  unfold words
  split_ifs <;> apply triple_transport

theorem combined_supported (x : Fin (a i.val) → Bool) (y : Fin (a j.val) → Bool)
    (hx : G i x≠0) (hy : G j y≠0) :
    (combined G i j r u).denote (combinedWord i j r u x y)≠0 := by
  apply C.supported_word
  intro v
  rw [words_value G i j r u x y v]
  split_ifs <;> assumption

theorem combined_missing (x : Fin (a i.val) → Bool) (y : Fin (a j.val) → Bool)
    (hr : 0<r) (hx : G i x=0) :
    (combined G i j r u).denote (combinedWord i j r u x y)=0 := by
  apply C.missing_word _ _ _ (Fin.castAdd u ⟨0,hr⟩)
  rw [words_value G i j r u x y (Fin.castAdd u ⟨0,hr⟩)]
  exact (if_pos hr).trans hx

theorem combined_central (hi : Signature.CentralSupport (G i))
    (hj : Signature.CentralSupport (G j)) :
    Signature.CentralSupport (combined G i j r u).denote := by
  apply C.central
  intro v
  refine Fin.addCases (fun v=>?_) (fun v=>?_) v
  · change Signature.CentralSupport (G (if v.val<r then i else j))
    rw [if_pos v.isLt]
    exact hi
  · have hn : ¬r+v.val<r := by omega
    change Signature.CentralSupport (G (if r+v.val<r then i else j))
    rw [if_neg hn]
    exact hj

theorem combined_arity : C.arity (a:=a) (labels i j r u)=r*a i.val+u*a j.val := by
  rw [C.arity_sum,Fin.sum_univ_add]
  simp [labels]

variable {G i j}
variable (T : Triple (G i)) (U : Triple (G j))

def firstCopies : ℕ := (charge U.xor).toNat
def secondCopies : ℕ := (-charge T.xor).toNat

def balancedLabels := labels i j (firstCopies U) (secondCopies T)
abbrev balancedGraph := C.graph (balancedLabels T U) G

def balancedTriple : Triple (balancedGraph T U).denote where
  first := combinedWord i j (firstCopies U) (secondCopies T) T.first U.first
  second := combinedWord i j (firstCopies U) (secondCopies T) T.second U.second
  third := combinedWord i j (firstCopies U) (secondCopies T) T.third U.third
  first_supported := combined_supported G i j _ _ _ _ T.first_supported U.first_supported
  second_supported := combined_supported G i j _ _ _ _ T.second_supported U.second_supported
  third_supported := combined_supported G i j _ _ _ _ T.third_supported U.third_supported

theorem balancedTriple_xor : (balancedTriple T U).xor=
    combinedWord i j (firstCopies U) (secondCopies T) T.xor U.xor :=
  combined_xor i j _ _ _ _ _ _ _ _

/-- No cancellation or scalar normalization occurs: the missing entry has a
literal zero original factor, while every chosen triple entry is a product
of nonzero original coefficients. -/
theorem balanced_hole (hT : G i T.xor=0) (hn : charge T.xor<0) (hp : 0<charge U.xor) :
    CentralHole (balancedGraph T U).denote := by
  refine ⟨balancedTriple T U,?_,?_⟩
  · rw [balancedTriple_xor]
    apply combined_missing G i j _ _ _ _ _ hT
    simp only [firstCopies]
    omega
  · rw [balancedTriple_xor,combined_charge]
    simp only [firstCopies,secondCopies,Int.toNat_of_nonneg (le_of_lt hp),
      Int.toNat_of_nonneg (by omega : 0≤ -charge T.xor)]
    ring

/-- Exact counts for the source construction in Lemma 54. -/
theorem balanced_resources :
    (balancedGraph T U).shape.vertices=firstCopies U+secondCopies T ∧
    (balancedGraph T U).shape.edges=0 ∧
    C.arity (a:=a) (balancedLabels T U)=firstCopies U*a i.val+secondCopies T*a j.val :=
  ⟨rfl,rfl,combined_arity i j _ _⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeSupportTensor
