import Mathlib.Tactic
import Mathlib.Init.Order.Defs

variable (γ : Type*)

--Familia de conjuntos indexada por I.
--Sea (i : I) entonces X i : Set γ
variable {I : Type*}
variable (X : I → Set γ)

variable (S : Set γ )

--Abrimos los espacios de nombres para usar los alias cortos.
open Set
open Classical




--Todo lo relativo al principio de buena ordenación, definir que una relación es buen orden para
--luego enunciar el principio de buena ordenación.
def is_well_ordered (R : γ  → γ → Prop) : Prop := ∀ (A : Set γ), Nonempty A → ∃ n ∈ A, ∀ m ∈ A, R n m
def well_ordered_principle : Prop := ∃ (R : γ  → γ → Prop), is_well_ordered γ R

--Por comodidad el tipo γ va a ser implícito a partir de aquí.
variable {γ}

--Definición del axioma de elección usando la familia indexada de conjuntos antes definida.
def axiom_of_choice : Prop := (∀ (i : I), Nonempty (X i)) → ∃ (f : (I → ⋃ i, X i)), ∀ (i : I), (f i).1 ∈ X i

--Definición de resultados previos (ser una cadena y ser inductivo) para luego poder formalizar
--el Lema de Zorn.
def is_chain [PartialOrder γ] (c : Set γ) : Prop := ∀ (x y : γ), x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x
def inductive_set [PartialOrder γ] (S : Set γ) : Prop := ∀ (c : Set γ), c ⊆ S → is_chain c → ∃ (ub : γ), ∀ (x : γ ), x ∈ c → x ≤ ub
def zorn [PartialOrder γ] (_ : inductive_set S ) : Prop := ∃ (m : γ), m ∈ S ∧ ∀ (x : γ), x ∈ S → x < m

theorem wop_aoc : well_ordered_principle γ → axiom_of_choice X := by
--Introducimos hipótesis
  rintro wop nempty

--Reescribimos el PBO y obtenemos la hipótesis de ser buen orden R.
  rw[well_ordered_principle] at wop
  obtain ⟨R,hR⟩ := wop
  rw[is_well_ordered] at hR

--Usamos refine' para dividir en submetas la meta actual
  refine' ⟨ fun i => _,_⟩

--Demostramos la primera meta eligiendo un elemento que cumpla la propiedad y con
--mem_iUnion podemos aplicar la propiedad particularizando en i.
  . use choose (hR (X i) (nempty i))
    rw [mem_iUnion]
    use i
    exact (choose_spec (hR (X i) (nempty i))).left
--Por el otro lado solo tenemos que aplicar la propiedad que se cumple para todo i.
  . dsimp
    intro i
    exact (choose_spec (hR (X i) (nempty i))).left

--Definimos los pares (s,r) de la literatura con las propiedades de que r es un buen orden
--de s y que los elementos externos de s no están relacionados.
@[ext]structure WellOrderedSet (γ : Type _) :=
(s : Set γ)
(r : γ  → γ  → Prop)
(h_well : is_well_ordered s (fun x y => r x.val y.val))
(h_triv : ∀ (x y : γ) (_ : x ∉ s ∨ y ∉ s), ¬ r x y)

--Conjunto que vamos a comprobar que es inductivo.
variable (F : Set (WellOrderedSet γ))

--Instancia de PartialOrden para poder ordenar los WellOrderedSet
instance : PartialOrder (WellOrderedSet γ) where
  le := fun x y => x.s ⊆ y.s ∧ ∀ (a b), x.r a b → y.r a b
  lt := fun x y => x.s ⊂ y.s ∧ ∀ (a b), x.r a b → y.r a b
  le_refl := by
    intro x
    simp only [imp_self, implies_true]
    apply And.intro
    . apply Set.Subset.refl
    trivial

  le_trans := by
    intro x y z hxy hyz
    dsimp only
    apply And.intro
    . apply Set.Subset.trans (And.left hxy) (And.left hyz)
    intro a b hxr
    apply And.right hyz a b
    apply And.right hxy a b
    exact hxr

  lt_iff_le_not_le := by
    intro x y
    apply Iff.intro
    . intro h
      apply And.intro
      . apply And.intro
        . simp at h
          exact And.left h.1
        intro a b hxr
        simp at h
        apply And.right h a b
        exact hxr
      intro h_le_yx
      have not_h_s := And.right (And.left h)
      have h_s := And.left h_le_yx
      contradiction
    intro h
    apply And.intro
    . rw[ssubset_def]
      apply And.intro
      . exact h.1.1
      rw[not_subset]
      simp only [not_and, not_forall, exists_prop] at h
      by_cases hyx : y.s ⊆ x.s
      . have h2 := h.2 hyx
        rcases h2 with ⟨x1,x2,h_y_r,h_x_not_r⟩
        by_contra nota
        push_neg at nota
        have h3 := y.h_triv
        specialize h3 x1 x2
        rw[←not_imp_not] at h3
        simp only [not_not, not_or] at h3
        specialize h3 h_y_r
        have x1x : x1 ∈ x.s := by
          apply nota
          exact h3.1
        have x2x : x2 ∈ x.s := by
          apply nota
          exact h3.2
        have h4 := x.h_triv
        specialize h4 x1 x2
        --rw[←not_imp_not] at h4
        --simp only [not_not, not_or] at h4
        have h5 : x1 ∈ x.s ∧ x2 ∈ x.s := by
          apply And.intro x1x x2x
        sorry
      rwa[not_subset] at hyx
    intro a b hxab
    apply h.1.2
    exact hxab


  le_antisymm := by
    intro x y le_xy le_yx
    have s_eq : x.s = y.s := Set.Subset.antisymm le_xy.1 le_yx.1
    have r_eq : ∀ a b, (x.r a b ↔ y.r a b) := by
      intro a b
      apply Iff.intro
      . intro h
        exact le_xy.2 a b h
      intro h
      exact le_yx.2 a b h
    rcases x with ⟨x.s,x.r,x.hwell,x.htriv⟩
    rcases y with ⟨y.s,y.r,y.hwell,y.htriv⟩
    simp only [WellOrderedSet.mk.injEq]
    apply And.intro
    . exact s_eq
    ext a b
    apply r_eq


--Lema necesario para porbar que el conjunto F es inductivo.
lemma F_is_inductive : inductive_set F := by
  intro c h1 h2
  let A := ⋃ x ∈ c, x.s
  set R := fun a b => ∃ cᵢ, cᵢ ∈ c ∧ cᵢ.r a b with hR

  let ub : WellOrderedSet γ :={
    s:=A
    r:=R
    h_well:=by
      rw[is_well_ordered]
      intro Aᵢ hAᵢ_ne
      obtain ⟨n,hn⟩ := hAᵢ_ne
      use n
      apply And.intro
      . apply hn
      intro m hm
      rw[hR]
      dsimp only
      have h_n : ∃ x ∈ c, n.1 ∈ x.s := by
        simp only at n
        obtain ⟨x1, hx1⟩ := n
        rw[mem_iUnion] at hx1
        obtain ⟨x, hx⟩ := hx1
        use x
        rw[mem_iUnion] at hx
        obtain ⟨xc,x1s⟩ := hx
        apply And.intro
        . exact xc
        exact x1s
      have h_m : ∃ x ∈ c, m.1 ∈ x.s := by
        simp only at m
        obtain ⟨x1, hx1⟩ := m
        rw[mem_iUnion] at hx1
        obtain ⟨x, hx⟩ := hx1
        use x
        rw[mem_iUnion] at hx
        obtain ⟨xc,x1s⟩ := hx
        apply And.intro
        . exact xc
        exact x1s
      obtain ⟨cₙ, hcₙ⟩ := h_n
      obtain ⟨cₘ, hcₘ⟩ := h_m
      have h_chain := h2 cₙ cₘ hcₙ.left hcₘ.left
      rcases h_chain with hleft | hright
      --Busco encontrar que estan relacionados
      . use cₙ
        apply And.intro hcₙ.1
        sorry
      use cₘ
      sorry
    h_triv := by
      intro a1 a2 h
      simp only [not_exists, not_and]
      intro cᵢ hcᵢ
      have h_triv := cᵢ.h_triv
      apply h_triv
      rw[mem_iUnion,mem_iUnion] at h
      simp only [mem_iUnion, exists_prop, not_exists, not_and] at h
      rcases h with hleft | hright
      . apply Or.intro_left
        apply hleft
        exact hcᵢ
      apply Or.intro_right
      apply hright
      exact hcᵢ
  }
  use ub
  intro y hy
  apply And.intro
  . simp only
    exact subset_biUnion_of_mem hy
  intro a b hyr
  simp only
  use y

--Demostración de la implicación LZ → PBO utilizando que F es inductivo
theorem zorn_implies_wop : zorn F (F_is_inductive F) → well_ordered_principle γ := by

--Obtenemos las hipótesis del Lema de Zorn, un m maximal y hm la propiedad de ser maximal.
  intro hZ
  rw[zorn] at hZ
  rw[well_ordered_principle]
  obtain ⟨m, hm⟩ := hZ

--Probamos que m.s es todo el universo.
  have : m.s = Set.univ := by
    apply eq_univ_of_forall
    intro x
    by_contra hx
    have h := hm.2
    let M : WellOrderedSet γ := {
      --Añado x al conjunto m.s
      s:= {x} ∪ m.s
      --x es el elemento más grande del conjunto
      r:= fun a b => if a = x then false else if b = x then true else m.r a b


      h_well := by
        rw[is_well_ordered]
        intro A hA_ne
        have h3 := m.3
        rw[is_well_ordered] at h3
        sorry


      h_triv := by
        intro a b h1
        simp
        intro ha
        have h2 := m.4
        specialize h2 a b
        apply And.intro
        . sorry
        apply h2
        apply Or.intro_left
        apply Or.elim h1
        . sorry
        sorry

    }
    have hmM : m ≤ M := by
      apply And.intro
      . simp only [singleton_union, subset_insert]
      intro a b mr
      simp only [Bool.ite_eq_true_distrib, ite_eq_left_iff, decide_eq_true_eq, if_false_left_eq_and]
      apply And.intro
      . sorry
      sorry
    have hMF : M ∈ F := sorry
    have hMm : M < m := by
      apply h
      exact hMF
    simp only[LE.le] at hmM
    simp only[LT.lt] at hMm
    have h1 := hMm.1
    have h2 : x ∈ m.s := by
      have : {x} ∪ m.s ⊆ m.s := by
        exact subset_of_ssubset h1
      rw[union_subset_iff] at this
      simp only [singleton_subset_iff] at this
      exact this.1
    contradiction

--Utilizamos la relación de m (m.r) que será la que cumpla lo que pide la meta.
  use m.r

--Sabemos que m es un buen orden por construcción
  have h3 := m.3

--Aplicamos que m.s = univ γ
  rw[this] at h3

--Tenemos que ↑univ es equivalente a γ
  have equiv := Equiv.Set.univ γ

--Ver si puedo usar la equivalencia de alguna manera son Equiv.Set.univ
  sorry

theorem aoc_implies_zorn : axiom_of_choice X → zorn F (F_is_inductive F) := by
  sorry

variable (A : I → Set γ )
variable (φ : Set γ  → Set γ )

lemma key_lemma [PartialOrder γ] (h₁ : (∀ (i : I), Nonempty (A i)) → is_chain (A i) → ∃ (j : I), A j = ⋃ i, A i) (h₂ : ∀ (i : I), (A i) ⊆ φ (A i))
(h₃ : ∀(i : I), ∅ = (φ (A i) \ (A i)) ∨ ∃! (a : γ), a ∈ (φ (A i) \ (A i))) : ∃ (i : I), φ (A i) = (A i) := by
  sorry
