# latte-compiler
Kompilator języka latte.

Zaimplementowane rozszerzenia:
- tablice
- obiektowość, w tym struktury, dziedziczenie i metody wirtualne
- sprowadzanie kodu do postaci SSA
- optymalizacje:
    - propagacja stałych
    - upraszczanie wyrażeń
    - eliminacja wspólnych podwyrażeń
    - usuwanie niepotrzebnych skoków
    - usuwanie nieużywanych zmiennych
    - wywoływanie metod w sposób wirtualny tylko wtedy gdy były nadpisania
    - usuwanie nieosiągalnego kodu
    - optymalizacja rekurencji ogonowej
    - zastąpienie bloku "if(c) v = v1 else v = v2" instrukcją select gdy v1 i v2 są bez efektów ubocznych 
    
Wykorzystane moduły:
    - moduł MyLlvm to kopia modułu https://gitlab.haskell.org/ghc/ghc/tree/master/compiler/llvmGen
        rozszerzona między innymi o instrukcję Select, inservalue i poprawę drobnego błędu generacji SDoc