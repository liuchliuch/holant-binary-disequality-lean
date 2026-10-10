import Holant.Proofs.Hardness.GeneralOddResidueGcd
import Holant.ChargeConservation

/-! Exact support-lattice conservation for actual open native networks.
The original support gcd is an obstruction to all unary graphs, not merely to
the particular loop or gcd descent. No synthetic pin is used in the proof. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueConservation
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource GeneralOddResidueGcd
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The incidence bijection counts all external ports and both distinct ends
of every internal edge, including loops and parallel edges. -/
theorem sum_balance {n : ℕ} (S : NetworkShape n) (b : Bool)
    (x : Fin n→Bool) (z : (Fin S.edges×Bool)→Bool)
    (hz : ∀e,z (e,false)≠z (e,true)) :
    (∑v,balance b (S.assignment x z v))=balance b x := by
  unfold balance NetworkShape.assignment
  rw [←Fintype.sum_sigma (fun p=>
    if Sum.elim x z (S.ports p)=b then (1 : ℤ) else -1)]
  rw [S.ports.sum_comp (fun q=>if Sum.elim x z q=b then (1 : ℤ) else -1),
    Fintype.sum_sum_type,Fintype.sum_prod_type]
  have he : ∀e : Fin S.edges,
      (∑t : Bool,if z (e,t)=b then (1 : ℤ) else -1)=0 := by
    intro e
    have h := hz e
    cases b <;> cases h0 : z (e,false) <;> cases h1 : z (e,true) <;>
      simp_all
  change balance b x + (∑e : Fin S.edges,∑t : Bool,
    if z (e,t)=b then (1 : ℤ) else -1)=balance b x
  simp only [he,Finset.sum_const_zero,add_zero]

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- A nonzero boundary coefficient contains a genuine nonzero assignment
term. Charge divisibility at each original vertex therefore passes through
the finite state sum, even when other terms cancel. -/
theorem divides_boundary (F : SignatureFamily K) (d : ℤ) (b : Bool)
    (hdiv : ∀g∈F,∀x,g.2 x≠0 → d∣balance b x)
    (N : Network K n) (hNF : Uses N F) (hNX : Native N)
    (x : Fin n→Bool) (hx : N.denote x≠0) : d∣balance b x := by
  have hex : ∃z,N.assignmentTerm x z≠0 := by
    by_contra h
    push Not at h
    apply hx
    exact Finset.sum_eq_zero (fun z _=>h z)
  obtain ⟨z,hz⟩ := hex
  have hop : ∀e,z (e,false)≠z (e,true) := by
    intro e he
    have h := N.edge_ne_zero_of_assignmentTerm_ne_zero x z hz e
    rw [hNX e] at h
    exact h (by simp [Signature.disequality,he])
  rw [←sum_balance N.shape b x z hop]
  apply Finset.dvd_sum
  intro v _
  exact hdiv ⟨N.shape.arity v,N.vertex v⟩ (hNF v) _
    (N.vertex_ne_zero_of_assignmentTerm_ne_zero x z hz v)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- The computed original support gcd divides every supported charge of every
actual graph over that original family. -/
theorem original_graph (N : Network AlgebraicComplex n)
    (hNF : Uses N (original G)) (hNE : Ordinary N)
    (x : Fin n→Bool) (hx : sourceKBasis.symm.action N.denote x≠0) :
    (supportGcd G : ℤ)∣balance true x := by
  apply divides_boundary (kCoordinates (original G)) (supportGcd G) true _
    (toNative N) (toNative_uses (original G) N hNF) (toNative_native N hNE) x
    (by rwa [toNative_denote])
  rintro g ⟨f,⟨k,rfl⟩,rfl⟩ y hy
  exact (dvd_supportGcd_iff G _).mp (dvd_refl _) k y hy

/-- A nonzero actual ordinary unary is possible only for primitive original
support charges. This supplies the converse to the new unary producer. -/
theorem unary_forces_primitive (U : Network AlgebraicComplex 1)
    (hUF : Uses U (original G)) (hUE : Ordinary U) (hU : U.denote≠0) :
    supportGcd G=1 := by
  have hchart : sourceKBasis.symm.action U.denote≠0 := by
    intro h
    apply hU
    have he := congrArg sourceKBasis.action h
    rw [InvertibleKernel.action_symm_action] at he
    exact he.trans (Signature.coordinateAction_zero _)
  have hex : ∃x,sourceKBasis.symm.action U.denote x≠0 := by
    by_contra h
    push Not at h
    exact hchart (funext h)
  obtain ⟨x,hx⟩ := hex
  have hd := original_graph G U hUF hUE x hx
  rw [unary_word x] at hd
  cases hb : x 0 <;> simp only [balance,Fin.sum_univ_one,hb,Bool.false_eq_true,ite_false,ite_true] at hd
  · have hdn : (supportGcd G : ℤ)∣(1 : ℤ) := dvd_neg.mp hd
    have hn : supportGcd G∣1 := by exact_mod_cast hdn
    exact Nat.dvd_one.mp hn
  · have hn : supportGcd G∣1 := by exact_mod_cast hd
    exact Nat.dvd_one.mp hn

/-- A supported constant boundary word exposes the whole arity as an original
support-lattice multiple. -/
theorem constant_graph (N : Network AlgebraicComplex n)
    (hNF : Uses N (original G)) (hNE : Ordinary N) (b : Bool)
    (hb : sourceKBasis.symm.action N.denote (fun _=>b)≠0) : supportGcd G∣n := by
  have hd := original_graph G N hNF hNE (fun _=>b) hb
  cases b
  · simp only [balance,Bool.false_eq_true,ite_false,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_neg,mul_one] at hd
    exact_mod_cast dvd_neg.mp hd
  · simp only [balance,ite_true,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one] at hd
    exact_mod_cast hd

/-- With both signs present, the minimal nonzero odd graph has exactly the
finite original support gcd as its arity. -/
theorem minimal_arity_eq_supportGcd (D : GeneralOddMinimalTerminal.Minimal G)
    (hside : ¬CommonOneSided (kCoordinates (original G))) : D.arity=supportGcd G := by
  apply Nat.dvd_antisymm (minimal_dvd_supportGcd G D hside)
  by_cases h1 : D.arity=1
  · let U := reboundary D.graph (finCongr h1)
    have hU : U.denote≠0 := by
      intro hz
      apply D.nonzero
      funext x
      have he := congrFun hz (fun i=>x ((finCongr h1).symm i))
      simpa only [U,reboundary_denote,Equiv.symm_apply_apply,Pi.zero_apply] using he
    have hp := unary_forces_primitive G U D.uses D.ordinary hU
    rw [hp]
    exact one_dvd _
  · have hh : 3≤D.arity := by obtain ⟨k,hk⟩ := D.odd; omega
    obtain ⟨b,hb⟩ := GeneralOddMinimalTerminal.supported_endpoint G D hh
    exact constant_graph G D.graph D.uses D.ordinary (!b) hb

/-- Both signs and an odd source force the exact charge lattice to have a
positive odd generator, witnessed by a real minimal graph. -/
theorem supportGcd_positive_odd (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hside : ¬CommonOneSided (kCoordinates (original G))) :
    0<supportGcd G ∧ Odd (supportGcd G) := by
  let D := GeneralOddMinimalTerminal.select G j ho hnz
  have he := minimal_arity_eq_supportGcd G D hside
  have hod : Odd (supportGcd G) := he ▸ D.odd
  exact ⟨by obtain ⟨k,hk⟩ := hod; omega,hod⟩

/-- Exact primitive-charge/unary equivalence once both signs and one nonzero
odd original row are present. A nonprimitive lattice cannot be resolved by
assuming access to an ordinary unary. -/
theorem unary_iff_primitive (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hside : ¬CommonOneSided (kCoordinates (original G))) :
    (∃U : GeneralOddHighTerminalAccess.Actual G 1,U.graph.denote≠0) ↔ supportGcd G=1 := by
  constructor
  · rintro ⟨U,hU⟩
    exact unary_forces_primitive G U.graph U.uses U.ordinary hU
  · intro h
    obtain ⟨U,hU,_⟩ := source_unary G j ho hnz hside h
    exact ⟨U,hU⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueConservation
