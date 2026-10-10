import Holant.Tensor

/-!
Boolean binary kernels and local bilinear change-of-basis identities.

The conventions follow the manuscript's holographic-transformation subsection and
ordered binary-chain discussion: column vectors transform by `M`, and an edge
pulls back to `Mᵀ E M`. All pairings are bilinear, with no conjugation. The
change-of-basis theorem below is local; it does not assert a network theorem.
-/

namespace Holant

/-- A binary table with explicitly ordered Boolean row and column indices. -/
abbrev Kernel (K : Type*) := Bool → Bool → K

namespace Kernel

variable {K : Type*}

/-- Exchange the two ordered ports; this is ordinary transpose. -/
def transpose (A : Kernel K) : Kernel K := fun a b => A b a

@[simp] theorem transpose_apply (A : Kernel K) (a b : Bool) :
    transpose A a b = A b a := rfl

@[simp] theorem transpose_transpose (A : Kernel K) : transpose (transpose A) = A := rfl

/-- Genuine two-by-two matrix multiplication, including its internal bit sum. -/
def mul [Semiring K] (A B : Kernel K) : Kernel K :=
  fun a c => ∑ b : Bool, A a b * B b c

/-- The ordinary column-vector action. -/
def act [Semiring K] (A : Kernel K) (u : Bool → K) : Bool → K :=
  fun a => ∑ b : Bool, A a b * u b

section Semiring

variable [Semiring K]

theorem mul_apply (A B : Kernel K) (a c : Bool) :
    mul A B a c = A a false * B false c + A a true * B true c := by
  simp [mul, add_comm]

theorem act_apply (A : Kernel K) (u : Bool → K) (a : Bool) :
    act A u a = A a false * u false + A a true * u true := by
  simp [act, add_comm]

theorem mul_assoc (A B C : Kernel K) : mul (mul A B) C = mul A (mul B C) := by
  funext a b
  simp [mul, add_mul, mul_add, _root_.mul_assoc, add_assoc, add_comm, add_left_comm]

@[simp] theorem equality_mul (A : Kernel K) : mul Signature.equality A = A := by
  funext a b
  cases a <;> simp [mul, Signature.equality]

@[simp] theorem mul_equality (A : Kernel K) : mul A Signature.equality = A := by
  funext a b
  cases b <;> simp [mul, Signature.equality]

@[simp] theorem act_equality (u : Bool → K) : act Signature.equality u = u := by
  funext a
  cases a <;> simp [act, Signature.equality]

theorem act_mul (A B : Kernel K) (u : Bool → K) : act (mul A B) u = act A (act B u) := by
  funext a
  simp [mul, act, add_mul, mul_add, _root_.mul_assoc, add_assoc, add_comm, add_left_comm]

@[simp] theorem transpose_equality : transpose (Signature.equality (K := K)) =
    Signature.equality := by
  funext a b
  cases a <;> cases b <;> rfl

@[simp] theorem transpose_disequality : transpose (Signature.disequality (K := K)) =
    Signature.disequality := by
  funext a b
  cases a <;> cases b <;> rfl

theorem disequality_mul (A : Kernel K) (a b : Bool) :
    mul Signature.disequality A a b = A (!a) b := by
  cases a <;> simp [mul, Signature.disequality]

theorem mul_disequality (A : Kernel K) (a b : Bool) :
    mul A Signature.disequality a b = A a (!b) := by
  cases b <;> simp [mul, Signature.disequality]

@[simp] theorem disequality_mul_disequality :
    mul (Signature.disequality (K := K)) Signature.disequality = Signature.equality := by
  funext a b
  cases a <;> cases b <;> simp [mul, Signature.disequality, Signature.equality]

@[simp] theorem act_disequality (u : Bool → K) (a : Bool) :
    act Signature.disequality u a = u (!a) := by
  cases a <;> simp [act, Signature.disequality]

/-- Deleting a local free-end wire applies its involutive kernel twice. -/
theorem act_act_of_mul_self_eq_equality (W : Kernel K)
    (hW : mul W W = Signature.equality) (u : Bool → K) :
    act W (act W u) = u := by
  rw [← act_mul, hW, act_equality]

@[simp] theorem act_act_equality (u : Bool → K) :
    act Signature.equality (act Signature.equality u) = u := by simp

@[simp] theorem act_act_disequality (u : Bool → K) :
    act Signature.disequality (act Signature.disequality u) = u :=
  act_act_of_mul_self_eq_equality Signature.disequality disequality_mul_disequality u

/-- Local isolated-edge box normalization for a symmetric involutive wire kernel.
This is a binary-table identity, with no assertion about network gluing. -/
theorem box_normalization (W : Kernel K) (hW : mul W W = Signature.equality)
    (hT : transpose W = W) : mul (mul W W) (transpose W) = W := by
  rw [hW, equality_mul, hT]

@[simp] theorem equality_box_normalization :
    mul (mul (Signature.equality (K := K)) Signature.equality)
      (transpose Signature.equality) = Signature.equality := by simp

@[simp] theorem disequality_box_normalization :
    mul (mul (Signature.disequality (K := K)) Signature.disequality)
      (transpose Signature.disequality) = Signature.disequality := by simp

/-- Attaching two native disequality edges complements both boundary bits. -/
theorem disequality_sandwich (A : Kernel K) (a b : Bool) :
    mul (mul Signature.disequality A) Signature.disequality a b = A (!a) (!b) := by
  rw [mul_disequality, disequality_mul]

/-- Exchanging a closing gadget's boundary order transposes it before attachment. -/
theorem disequality_transpose_sandwich (A : Kernel K) (a b : Bool) :
    mul (mul Signature.disequality (transpose A)) Signature.disequality a b =
      A (!b) (!a) := by
  rw [disequality_sandwich]
  rfl

/-- The bilinear Frobenius pairing, without conjugation. -/
def pair (A B : Kernel K) : K := ∑ a : Bool, ∑ b : Bool, A a b * B a b

/-- Matrix trace, with both Boolean diagonal entries retained. -/
def trace (A : Kernel K) : K := ∑ a : Bool, A a a

theorem pair_eq_trace (A B : Kernel K) : pair A B = trace (mul (transpose A) B) := by
  simp [pair, trace, mul, add_assoc, add_comm, add_left_comm]

/-- The existing ordered first-two-port contraction is a bilinear slice pairing. -/
theorem contract_eq_pair {n : ℕ} (E : Kernel K) (f : Signature K (n + 2))
    (x : Fin n → Bool) :
    Signature.contract E f x = pair E (fun a b => f (Fin.cons a (Fin.cons b x))) := rfl

end Semiring

section CommSemiring

variable [CommSemiring K]

theorem transpose_mul (A B : Kernel K) :
    transpose (mul A B) = mul (transpose B) (transpose A) := by
  funext a b
  simp [mul, _root_.mul_comm]

/-- Two inward-ordered binary tensors joined by an edge. -/
def join (E L R : Kernel K) : Kernel K := fun a b => Signature.connect E (L a) (R b)

/-- Inward ordering gives `L E Rᵀ`, not `L E R`. -/
theorem join_eq_mul (E L R : Kernel K) : join E L R = mul (mul L E) (transpose R) := by
  funext a b
  simp [join, Signature.connect, mul, mul_add,
    _root_.mul_comm, _root_.mul_left_comm, add_assoc, add_comm, add_left_comm]

/-- Pull back a genuine weighted edge by applying `M` to both endpoint columns. -/
def pullback (E M : Kernel K) : Kernel K := mul (mul (transpose M) E) M

theorem pullback_equality (M : Kernel K) :
    pullback Signature.equality M = mul (transpose M) M := by
  simp [pullback]

/-- Moving two column actions across a bilinear connection transforms its edge. -/
theorem connect_act (E A B : Kernel K) (u v : Bool → K) :
    Signature.connect E (act A u) (act B v) =
      Signature.connect (mul (mul (transpose A) E) B) u v := by
  simp only [Signature.connect, act, mul, transpose_apply, Fintype.sum_bool, mul_add, add_mul]
  ac_rfl

theorem connect_act_same (E M : Kernel K) (u v : Bool → K) :
    Signature.connect E (act M u) (act M v) = Signature.connect (pullback E M) u v :=
  connect_act E M M u v

/-- Left signatures use the dual action `Mᵀ`, so the two bipartite actions cancel. -/
theorem connect_dual_change_basis (M N : Kernel K)
    (hMN : mul M N = Signature.equality) (g f : Bool → K) :
    Signature.connect Signature.equality (act (transpose M) g) (act N f) =
      Signature.connect Signature.equality g f := by
  rw [connect_act, transpose_transpose, mul_equality, hMN]

/-- Local holographic cancellation under an actual matrix inverse identity.
Only the displayed right-inverse identity is needed for this orientation. -/
theorem connect_change_basis (E M N : Kernel K)
    (hMN : mul M N = Signature.equality) (u v : Bool → K) :
    Signature.connect (pullback E M) (act N u) (act N v) = Signature.connect E u v := by
  rw [← connect_act_same, ← act_mul, ← act_mul, hMN, act_equality, act_equality]

/-- The equality-edge specialization has the weighted transformed edge `MᵀM`. -/
theorem connect_equality_change_basis (M N : Kernel K)
    (hMN : mul M N = Signature.equality) (u v : Bool → K) :
    Signature.connect (mul (transpose M) M) (act N u) (act N v) =
      Signature.connect Signature.equality u v := by
  simpa only [pullback_equality] using connect_change_basis Signature.equality M N hMN u v

/-- The native-edge specialization retains the genuine weighted edge `MᵀXM`. -/
theorem connect_disequality_change_basis (M N : Kernel K)
    (hMN : mul M N = Signature.equality) (u v : Bool → K) :
    Signature.connect (pullback Signature.disequality M) (act N u) (act N v) =
      Signature.connect Signature.disequality u v :=
  connect_change_basis Signature.disequality M N hMN u v

end CommSemiring
end Kernel
end Holant
