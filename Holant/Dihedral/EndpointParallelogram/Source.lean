import Holant.Dihedral.EndpointParallelogram.Cards
import Holant.Tensor
import Mathlib.Tactic.Ring

/-! Main-text Lemma 6.12 with actual card sums, original port order and exact
nonzero representative scalars. Physical availability is attached to the actual
sampled cards; no endpoint slice is asserted to be a gadget. -/
namespace Holant.Dihedral.EndpointParallelogram
open Holant

/-- Exact Boolean/binary-field coordinate bridge. -/
def bitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z ≠ 0)
  left_inv b := by cases b <;> decide
  right_inv z := by fin_cases z <;> rfl

def bitsEquiv (ι : Type*) : (ι → Bool) ≃ (ι → ZMod 2) :=
  Equiv.arrowCongr (Equiv.refl ι) bitEquiv

@[simp] theorem bitsEquiv_apply (ι : Type*) (x : ι → Bool) (i : ι) :
    bitsEquiv ι x i = bitEquiv (x i) := rfl
@[simp] theorem bitsEquiv_symm_apply (ι : Type*) (x : ι → ZMod 2) (i : ι) :
    (bitsEquiv ι).symm x i = bitEquiv.symm (x i) := rfl

variable {K : Type*} [Field K] {n : ℕ}

def slice (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (a b : Bool) : (Fin n → ZMod 2) → K := fun x =>
  q (fun i => (Fin.cons a (Fin.cons b ((bitsEquiv (Fin n)).symm x)) : Fin (n+2) → Bool) (ports.symm i))

/-- The literal sampled I(t)/X(t) kernel in the fixed ordered sector basis. -/
def phaseKernel (odd : Bool) (t : K) (a b : Bool) : K :=
  if (a ^^ b) = odd then (if a then t else 1) else 0

/-- The actual two-bit contraction sum on the original q. -/
def card (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (odd : Bool) (t κ : K) : Signature K n := fun x =>
  ∑ a : Bool, ∑ b : Bool, κ * phaseKernel odd t a b *
    q (fun i => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) (ports.symm i))

theorem card_even (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (t κ : K) (x : Fin n → ZMod 2) :
    card q ports false t κ ((bitsEquiv (Fin n)).symm x) =
      pencil (slice q ports false false) (slice q ports true true) t κ x := by
  simp [card,phaseKernel,Fintype.sum_bool,slice,pencil]
  ring

theorem card_odd (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (s κ : K) (x : Fin n → ZMod 2) :
    card q ports true s κ ((bitsEquiv (Fin n)).symm x) =
      pencil (slice q ports false true) (slice q ports true false) s κ x := by
  simp [card,phaseKernel,Fintype.sum_bool,slice,pencil]
  ring

/-- The hypothesis names the residual matching of a physical card by its full
support, allowing arbitrary nonzero coefficients on that support. -/
def CardMatching (f : Signature K n) (M : Pairing (Fin n)) (offset : Fin n → ZMod 2) : Prop :=
  fullCoset (fun x => f ((bitsEquiv (Fin n)).symm x)) M.code offset

/-- Source 6.12. The complementary-axis hypotheses concern analytic slices;
the compared matchings and physical provenance concern the actual phase cards.
Failure yields different matchings on these same two actual nonzero gadgets. -/
theorem source_actual_card_endpoint_test
    (F : SignatureFamily K) (W : EdgeKind)
    (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (a b c d : Fin n → ZMod 2)
    (hA : fullCoset (slice q ports false false) L a)
    (hB : fullCoset (slice q ports false true) L b)
    (hC : fullCoset (slice q ports true false) L c)
    (hD : fullCoset (slice q ports true true) L d)
    (hE : a+d ∉ L) (hO : b+c ∉ L)
    (t s κE κO : K) (ht : t ≠ 0) (hs : s ≠ 0) (hκE : κE ≠ 0) (hκO : κO ≠ 0)
    (ME MO : Pairing (Fin n)) (e o : Fin n → ZMod 2)
    (hmE : CardMatching (card q ports false t κE) ME e)
    (hmO : CardMatching (card q ports true s κO) MO o)
    (physicalE : Gadget.Realizes F W (card q ports false t κE))
    (physicalO : Gadget.Realizes F W (card q ports true s κO)) :
    (ME = MO ↔ a+b+c+d ∈ L) ∧
    card q ports false t κE ≠ 0 ∧ card q ports true s κO ≠ 0 ∧
    (a+b+c+d ∉ L →
      Gadget.Realizes F W (card q ports false t κE) ∧
      Gadget.Realizes F W (card q ports true s κO) ∧ ME ≠ MO) := by
  have hmE' : fullCoset
      (pencil (slice q ports false false) (slice q ports true true) t κE) ME.code e := by
    simpa only [CardMatching,fullCoset,card_even] using hmE
  have hmO' : fullCoset
      (pencil (slice q ports false true) (slice q ports true false) s κO) MO.code o := by
    simpa only [CardMatching,fullCoset,card_odd] using hmO
  have hh := actual_card_endpoint_test L a b c d _ _ _ _ hA hB hC hD hE hO
    t s κE κO ht hs hκE hκO ME MO e o hmE' hmO'
  refine ⟨hh,?_,?_,fun hn => ⟨physicalE,physicalO,fun he => hn (hh.mp he)⟩⟩
  · intro hz
    have hn := pencil_nonzero L a d _ _ hA hD hE t κE ht hκE
    apply hn
    funext x
    rw [← card_even,hz]
    rfl
  · intro hz
    have hn := pencil_nonzero L b c _ _ hB hC hO s κO hs hκO
    apply hn
    funext x
    rw [← card_odd,hz]
    rfl

end Holant.Dihedral.EndpointParallelogram
