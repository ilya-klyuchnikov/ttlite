isSublist p s = m p s p s
  where
    m []     ss     op os           = True
    m (p:pp) []     op os           = False
    m (p:pp) (s:ss) op os | p == s  = m pp ss op os
    m (p:pp) (s:ss) op os           = n op os
    
    n op []     = False
    n op (s:ss) = m op ss op ss
