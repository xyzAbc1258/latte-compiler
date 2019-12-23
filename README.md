# latte-compiler
Kompilator języka latte.

Zaimplementowane rozszerzenia:
- tablice
- obiektowość, w tym struktury, dziedziczenie i metody wirtualne
- sprowadzanie kodu do postaci SSA
- optymalizacje:
    - propagacja stałych
    - upraszczanie wyrażeń
    - usuwanie niepotrzebnych skoków
    - wywoływanie metod w sposób wirtualny tylko wtedy gdy były nadpisania
    - usuwanie nieosiągalnego kodu
    - eliminacja wspólnych podwyrażeń