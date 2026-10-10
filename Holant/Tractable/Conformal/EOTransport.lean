import Holant.Tractable.Conformal.CommonBasis
import Mathlib.Logic.Equiv.Bool

/-! Family-wide sign and oriented-pair transport of the literal EO predicate. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

/-- A single orientation choice is shared by all signatures and ports. -/
def flipWord {n : ℕ} (opposite : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  if opposite then complementWord x else x

@[simp] theorem flipWord_false {n : ℕ} (x : Fin n → Bool) : flipWord false x = x := rfl
@[simp] theorem flipWord_true {n : ℕ} (x : Fin n → Bool) :
    flipWord true x = complementWord x := rfl

@[simp] theorem flipWord_twice {n : ℕ} (opposite : Bool) (x : Fin n → Bool) :
    flipWord opposite (flipWord opposite x) = x := by cases opposite <;> simp

theorem flipWord_tripleXor {n : ℕ} (opposite : Bool) (a b c : Fin n → Bool) :
    tripleXor (flipWord opposite a) (flipWord opposite b) (flipWord opposite c) =
      flipWord opposite (tripleXor a b c) := by
  cases opposite
  · rfl
  · funext j
    cases ha : a j <;> cases hb : b j <;> cases hc : c j <;>
      simp [flipWord, tripleXor, complementWord, ha, hb, hc]

def oppositeSign : EOSign → EOSign
  | .positive => .negative
  | .negative => .positive

def transportSign (opposite : Bool) (sign : EOSign) : EOSign :=
  if opposite then oppositeSign sign else sign

theorem transportSign_charge {n : ℕ} (opposite : Bool) (sign : EOSign)
    (x : Fin n → Bool) :
    (transportSign opposite sign).value * Holant.charge x =
      sign.value * Holant.charge (flipWord opposite x) := by
  cases opposite
  · rfl
  · have hc : Holant.charge (complementWord x) = -Holant.charge x :=
      Holant.charge_compl x
    cases sign <;> simp [transportSign, oppositeSign, EOSign.value, hc]

/-- Reverse every oriented pair, retaining the original pairing and pair order. -/
def reversePairing {n : ℕ} (p : OrientedPerfectPairing n) : OrientedPerfectPairing n where
  count := p.count
  ports := (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot).trans p.ports

theorem reversePairing_word {n : ℕ} (p : OrientedPerfectPairing n)
    (z : Fin p.count → Bool) :
    (reversePairing p).word z = complementWord (p.word z) := by
  funext j
  change (if !(p.ports.symm j).2 then !(z (p.ports.symm j).1) else z (p.ports.symm j).1) =
    !(if (p.ports.symm j).2 then !(z (p.ports.symm j).1) else z (p.ports.symm j).1)
  cases (p.ports.symm j).2 <;> simp

def transportPairing {n : ℕ} (opposite : Bool) (p : OrientedPerfectPairing n) :
    OrientedPerfectPairing n := if opposite then reversePairing p else p

theorem eoClass_scale (C : EOClass) {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : C.Holds f) (c : AlgebraicComplex) : C.Holds (fun x => c * f x) := by
  cases C
  · exact Affine.scale h c
  · exact Product.scale h c

/-- Only a nonzero scalar and the one shared bit-complement choice may change. -/
def Related (opposite : Bool) (g h : AnySignature AlgebraicComplex) : Prop :=
  ∃ c : AlgebraicComplex, c ≠ 0 ∧
    h = ⟨g.1, fun x => c * g.2 (flipWord opposite x)⟩

theorem related_isEO {opposite : Bool} {g h : AnySignature AlgebraicComplex}
    (hrel : Related opposite g h) (hg : IsEO g) : IsEO h := by
  obtain ⟨c, hc, rfl⟩ := hrel
  refine ⟨hg.1, ?_⟩
  intro x hx
  change 2 * Holant.weight x ≠ g.1 at hx
  have hnot : 2 * Holant.weight (flipWord opposite x) ≠ g.1 := by
    cases opposite
    · exact hx
    · have hw : Holant.weight (complementWord x) + Holant.weight x = g.1 :=
        Holant.weight_compl_add x
      change 2 * Holant.weight (complementWord x) ≠ g.1
      omega
  simp only [hg.2 _ hnot, mul_zero]

/-- A transport lemma for the actual EO predicate. Its class witness and sign
remain outside both universals; reversing all ordered pairings avoids assuming
any closure of the source classes beyond their already-proved scalar closure. -/
theorem eoTract_transport {G H : SignatureFamily AlgebraicComplex}
    (hG : EOTract G) (hfin : H.Finite) (opposite : Bool)
    (hrel : ∀ h ∈ H, ∃ g ∈ G, Related opposite g h) : EOTract H := by
  obtain ⟨hGfin, hEO, sign, C, hxor, hpair⟩ := hG
  refine ⟨hfin, ?_, transportSign opposite sign, C, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hg, hgh⟩ := hrel h hh
    exact related_isEO hgh (hEO g hg)
  · intro h hh a b d ha hb hd
    obtain ⟨g, hg, c, hc, rfl⟩ := hrel h hh
    have hga := (mul_ne_zero_iff.mp ha).2
    have hgb := (mul_ne_zero_iff.mp hb).2
    have hgd := (mul_ne_zero_iff.mp hd).2
    have hx := hxor g hg (flipWord opposite a) (flipWord opposite b)
      (flipWord opposite d) hga hgb hgd
    rw [flipWord_tripleXor] at hx
    rcases hx with hx | hx
    · exact Or.inl (mul_ne_zero hc hx)
    · exact Or.inr (by simpa only [transportSign_charge] using hx)
  · intro h hh p
    obtain ⟨g, hg, c, hc, rfl⟩ := hrel h hh
    cases opposite
    · exact eoClass_scale C (hpair g hg p) c
    · have hp := eoClass_scale C (hpair g hg (reversePairing p)) c
      change C.Holds (fun z => c * g.2 ((reversePairing p).word z)) at hp
      change C.Holds (fun z => c * g.2 (complementWord (p.word z)))
      have he : (fun z : Fin p.count → Bool => c * g.2 ((reversePairing p).word z)) =
          (fun z => c * g.2 (complementWord (p.word z))) := by
        funext z
        exact congrArg (fun w => c * g.2 w) (reversePairing_word p z)
      exact he ▸ hp

theorem centralFamily_finite {G : SignatureFamily AlgebraicComplex} (hG : G.Finite) :
    (centralFamily G).Finite := by
  apply (hG.image (fun g : AnySignature AlgebraicComplex =>
    (⟨g.1, Signature.centralRestriction g.2⟩ : AnySignature AlgebraicComplex))).subset
  rintro h ⟨g, hg, _, rfl⟩
  exact ⟨g, hg, rfl⟩

theorem singleLayer_le_arity {n d : ℕ} {f : Signature AlgebraicComplex n}
    (hf : f ≠ 0) (hd : Signature.SingleLayer f d) : d ≤ n := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hw := hd.weight_of_nezero hx
  exact hw ▸ Holant.weight_le x

/-- Nonzero single-layer signatures have only layers `0,…,arity`, so ordered
completion preserves finiteness without any hidden choice of layer. -/
theorem completionFamily_finite {G : SignatureFamily AlgebraicComplex} (hG : G.Finite) :
    (completionFamily G).Finite := by
  let S : AnySignature AlgebraicComplex → Set (AnySignature AlgebraicComplex) :=
    fun g => (fun d => Signature.completeToEO g.2 d) '' Set.Iic g.1
  have hs : (⋃ g ∈ G, S g).Finite := hG.biUnion fun g _ => (Set.finite_Iic g.1).image _
  apply hs.subset
  rintro h ⟨g, hg, hnz, d, hd, rfl⟩
  exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg,
    ⟨d, singleLayer_le_arity hnz hd, rfl⟩⟩⟩

end Conformal
end
end Holant.Tractable
