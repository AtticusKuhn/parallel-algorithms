```agda
NatToLittleEndian (suc b) ∘ LittleEndianToNat (suc b)
≈ %2 ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule : (A ▵ B) ∘ C  ≈ (A ∘ C) ▵ (B ∘ C)
≈ %2 ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: %2 ∘ add ≈ xor ∘ twice %2
≈ xor ∘ twice %2 ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: twice A ∘ (B ⊗ C) ≈ (A ∘ B) ⊗ (A ∘ C)
≈ xor  ∘ ( %2 ∘ (if ∘ constʳ (p1 ▵ p0))  ⊗ ( %2 ∘ *2 ∘ LittleEndianToNat b ))  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: A ∘ if ∘ constʳ (B ▵ C) ≈ if ∘ constʳ (A ∘ B ▵ A ∘ C)
≈ xor  ∘ ( (if ∘ constʳ (%2 ∘ p1 ▵ %2 ∘ p0))  ⊗ ( %2 ∘ *2 ∘ LittleEndianToNat b ))  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: %2 ∘ p1 ≈ bit1 , %2 ∘ p0 ≈ bit0
≈ xor  ∘ ( (if ∘ constʳ (bit1 ▵ bit0))  ⊗ ( %2 ∘ *2 ∘ LittleEndianToNat b ))  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: %2 ∘ *2 ∘ A ≈ bit0
≈ xor  ∘ ( (if ∘ constʳ (bit1 ▵ bit0))  ⊗  bit0)  ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: xor ∘ (A ⊗ bit0) ≈ A
≈ ( (if ∘ constʳ (bit1 ▵ bit0)))   ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: if ∘ constʳ (bit1 ▵ bit0) ≈ id
≈ id   ▵ (NatToLittleEndian b ∘ /2) ∘ add ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: /2 ∘ add ≈ add ∘ twice /2
≈ id   ▵ (NatToLittleEndian b ) ∘ add ∘ twice /2 ∘ ((if ∘ constʳ (p1 ▵ p0))  ⊗ (*2 ∘ LittleEndianToNat b ))
Rule: twice A ∘ (B ⊗ C) = (A ∘ B) ⊗ (A ∘ C)
≈ id   ▵ (NatToLittleEndian b) ∘ add ∘ ( /2 ∘ (if ∘ constʳ (p1 ▵ p0))  ⊗ (/2 ∘ *2 ∘ LittleEndianToNat b ))
Rule: A ∘ if ∘ constʳ (B ▵ C) ≈ if ∘ constʳ (A ∘ B ▵ A ∘ C)
≈ id   ▵ (NatToLittleEndian b) ∘ add ∘ (  (if ∘ constʳ (/2 ∘ p1 ▵ /2 ∘ p0))  ⊗ (/2 ∘ *2 ∘ LittleEndianToNat b ))
Rule: /2 ∘ p1 ≈ p0 , /2 ∘ p0 ≈ p0
≈ id   ▵ (NatToLittleEndian b) ∘ add ∘ (  (if ∘ constʳ (p0 ▵ p0))  ⊗ (/2 ∘ *2 ∘ LittleEndianToNat b ))
Rule: /2 ∘ *2 ≈ id
≈ id   ▵ (NatToLittleEndian b) ∘ add ∘ (  (if ∘ constʳ (p0 ▵ p0))  ⊗ (LittleEndianToNat b ))
Rule: if ∘ constʳ (A ▵ A) ≈ A
≈ id   ▵ (NatToLittleEndian b) ∘ add ∘ (  p0  ⊗ (LittleEndianToNat b ))
Rule: add ∘ (p0 ⊗ A) ≈ A
≈ id   ▵ (NatToLittleEndian b) ∘  (LittleEndianToNat b )
Rule: NatToLittleEndian b ∘ LittleEndianToNat b ≈ id
≈ id   ▵ id
Rule: id ▵ id ≈ id
≈ id
```
