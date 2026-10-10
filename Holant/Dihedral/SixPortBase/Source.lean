import Holant.Dihedral.SixPortBase.Branches

/-! Manuscript Lemma 6.11, the direct standard-M_m six-port base. The complete
oriented physical phase deck alone yields a genuine exact 1+5 or 2+4 tensor
factorization. No sector classification, factor witness or protocol transition
is assumed, and no gadget access is inferred for either analytic factor. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
set_option backward.isDefEq.respectTransparency false

/-- The full algebraic theorem from literal original-port I/X-phase cards. -/
 theorem source_six_port_base {m : ℕ} (hm : 3≤m) (h : Signature Scalar 6)
    (hn : h ≠ 0) (hs : AllCards m h) : HasFactor h := by
  have hE := source_sector_type hm (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false)
    (hs.sector_samples false)
  have hO := source_sector_type hm (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true)
    (hs.sector_samples true)
  rcases hE with hzE | hpE | hcE
  · exact hs.zero_sector_factor hm hn (Equiv.refl _) false (by simpa using hzE)
  · obtain ⟨E⟩ := hpE
    rcases hO with hzO | hpO | hcO
    · exact hs.zero_sector_factor hm hn (Equiv.refl _) true (by simpa using hzO)
    · obtain ⟨O⟩ := hpO
      exact hs.proportional_factor hm hn E O
    · obtain ⟨O⟩ := hcO
      exact (hs.no_mixed_sector hm false E O).elim
  · obtain ⟨E⟩ := hcE
    rcases hO with hzO | hpO | hcO
    · exact hs.zero_sector_factor hm hn (Equiv.refl _) true (by simpa using hzO)
    · obtain ⟨O⟩ := hpO
      exact (hs.no_mixed_sector hm true O E).elim
    · obtain ⟨O⟩ := hcO
      exact hs.complementary_factor hm hn E O

 theorem source_no_six_port_prime {m : ℕ} (hm : 3≤m) (h : Signature Scalar 6)
    (hs : AllCards m h) : ¬TensorPrime h := by
  rintro ⟨hn,hprime⟩
  exact hprime (source_six_port_base hm h hn hs).proper

/-- The physical input retains one actual representative for every phase and
parity, all original input port permutations, and any recorded nonzero card
representative scalars. Actual normalization is a proved finite-sum identity. -/
 theorem physical_cards_normalized {m : ℕ} (hm : 3≤m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m) (h : Signature Scalar 6)
    (c : Equiv.Perm (Fin 6) → Bool → {t : Scalar // Roots m t} → Scalar)
    (hc : ∀ o γ t,c o γ t ≠ 0)
    (hs : ∀ o γ t,
      c o γ t • nativeCardValue (Tensor.reindex o.symm h) ((G.connections (by omega)).binary γ t)=0 ∨
      MatchingSample m 2 (c o γ t • nativeCardValue (Tensor.reindex o.symm h)
        ((G.connections (by omega)).binary γ t))) : AllCards m h := by
  let D := G.connections (by omega : 0<m)
  intro o γ t ht
  let z : {t : Scalar // Roots m t} := ⟨t,ht⟩
  have hz : c o γ z*D.multiplier γ z ≠ 0 := mul_ne_zero (hc o γ z) (D.multiplier_ne_zero γ z)
  have he : c o γ z • nativeCardValue (Tensor.reindex o.symm h) (D.binary γ z)=
      (c o γ z*D.multiplier γ z) • close γ t (Tensor.reindex o.symm h) := by
    rw [D.normalization,actual_close,smul_smul]
  have hh := hs o γ z
  change c o γ z • nativeCardValue (Tensor.reindex o.symm h) (D.binary γ z)=0 ∨
    MatchingSample m 2 (c o γ z • nativeCardValue (Tensor.reindex o.symm h) (D.binary γ z)) at hh
  rw [he] at hh
  rcases hh with hzq | hq
  · left
    by_contra hnon
    exact scalar_tensor_nonzero hz hnon hzq
  · right
    exact SectorRuling.MatchingSample.of_scale _ hz hq

/-- **Source Lemma 6.11** with actual fixed physical representatives. The
conclusion contains the literal original-port tensor equality and nonzero
factors of sizes 1+5 or 2+4; in particular the signature is not tensor-prime. -/
 theorem source_physical_six_port_base {m : ℕ} (hm : 3≤m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m) (h : Signature Scalar 6)
    (hn : h ≠ 0)
    (c : Equiv.Perm (Fin 6) → Bool → {t : Scalar // Roots m t} → Scalar)
    (hc : ∀ o γ t,c o γ t ≠ 0)
    (hs : ∀ o γ t,
      c o γ t • nativeCardValue (Tensor.reindex o.symm h) ((G.connections (by omega)).binary γ t)=0 ∨
      MatchingSample m 2 (c o γ t • nativeCardValue (Tensor.reindex o.symm h)
        ((G.connections (by omega)).binary γ t))) : HasFactor h ∧ ¬TensorPrime h := by
  have hd := physical_cards_normalized hm F G h c hc hs
  exact ⟨source_six_port_base hm h hn hd,source_no_six_port_prime hm h hd⟩

end Holant.Dihedral.SixPortBase
