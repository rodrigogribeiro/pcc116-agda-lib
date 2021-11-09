module Data.Generic.GMap where

  open import Data.Generic.Regular
  open import Data.Nat.Nat

  data [_⇒_] : ∀ {n} → Ctx n → Ctx n → Set where
    id : ∀ {n}{Γ : Ctx n} → [ Γ ⇒ Γ ]
    fun : ∀ {n}{S T : Reg n}
            {Γ Δ : Ctx n}
            (m : [ Γ ⇒ Δ ])
            (f : Data Γ S → Data Δ T) → [ Γ , S ⇒ Δ , T ]
    fmap : ∀ {n}{T : Reg n}{Γ Δ : Ctx n}(m : [ Γ ⇒ Δ ]) →
             [ Γ , T ⇒ Δ , T ]

  gmap : ∀ {n}{Γ Δ : Ctx n}{t : Reg n} → [ Γ ⇒ Δ ] → Data Γ t → Data Δ t
  gmap id (top d) = top d
  gmap (fun m f) (top d) = top (f d)
  gmap (fmap m) (top d) = top (gmap m d)
  gmap id (pop d) = pop d
  gmap (fun m f) (pop d) = pop (gmap m d)
  gmap (fmap m) (pop d) = pop (gmap m d)
  gmap m (def d) = def (gmap (fmap m) d)
  gmap m (inl d) = inl (gmap m d)
  gmap m (inr d) = inr (gmap m d)
  gmap m unit = unit
  gmap m (pair d d₁) = pair (gmap m d) (gmap m d₁)
  gmap m (rec d) = rec (gmap (fmap m) d )
