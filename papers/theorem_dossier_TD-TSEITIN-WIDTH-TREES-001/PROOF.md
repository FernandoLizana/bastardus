# Demostración: ancho de resolución de Tseitin en árboles y ciclos

**Estado:** R4–R5 parcial.  
- Cota inferior: demostración matemática directa.  
- Cota superior en árboles: demostración por inducción + **certificado constructivo** verificado por máquina (`constructive_proofs.py`).  
- Ciclos: demostración de existencia vía saturación de ancho 2 con padres explícitos (certificado comprobado).

**No demostramos** nada sobre P vs NP.

---

## Definiciones

Sea \(G=(V,E)\) un grafo no dirigido simple, conexo.

- Una **carga** es \(c:V\to\{0,1\}\).
- La **fórmula de Tseitin** \(T(G,c)\) introduce una variable booleana \(x_e\) por cada arista \(e\in E\).
- En cada vértice \(v\) se impone
  \[
  \bigoplus_{e\ni v} x_e \;=\; c(v)\pmod 2,
  \]
  codificada en CNF de la forma habitual: una cláusula de anchura \(\deg(v)\) por cada asignación prohibida de las aristas incidentes (hay \(2^{\deg(v)-1}\) cláusulas).

Hecho estándar: si \(G\) es conexo, \(T(G,c)\) es insatisfacible si y solo si \(\sum_v c(v)\) es impar.

Una **refutación por resolución** es una sucesión de cláusulas que empieza en los axiomas de \(T(G,c)\) y termina en la cláusula vacía \(\bot\), donde cada cláusula nueva es resolvente de dos anteriores.

El **ancho** de una refutación es el máximo número de literales en una cláusula de la sucesión.  
\(\mathrm{Width}(F)\) es el mínimo ancho entre todas las refutaciones de \(F\).

Sea \(\Delta(G)=\max_v \deg(v)\).

---

## Teorema A (cota inferior, general)

**Afirmación.** Para toda CNF \(F\), \(\mathrm{Width}(F)\ge w_{\mathrm{ax}}(F)\), donde \(w_{\mathrm{ax}}\) es la máxima anchura de una cláusula axioma.

**Prueba.** Toda refutación incluye los axiomas como pasos. El máximo no puede ser menor que el de un axioma. \(\square\)

**Corolario.** En \(T(G,c)\), hay axiomas de anchura \(\Delta(G)\). Luego
\[
\mathrm{Width}(T(G,c))\ge \Delta(G).
\]

---

## Lema B (sustitución Unit–XOR)

**Afirmación.** Sea \(d\ge 1\) y sea \(F\) el conjunto de cláusulas CNF que codifica
\[
z_0\oplus z_1\oplus\cdots\oplus z_{d-1}=b.
\]
Sea \(U\) la unidad \((z_0)\) o \((\neg z_0)\), que fija \(z_0=\chi\in\{0,1\}\).

Entonces, resolviendo \(U\) con cada cláusula de \(F\) que contiene el literal opuesto a \(U\), se obtienen exactamente las cláusulas CNF de
\[
z_1\oplus\cdots\oplus z_{d-1}=b\oplus\chi,
\]
cada una de anchura \(d-1\). Ningún resolvente supera anchura \(d\).

**Prueba.** Las cláusulas de \(F\) están en bijección con los patrones \(a\in\{0,1\}^d\) tales que \(\sum a\not\equiv b\pmod 2\): el patrón \(a\) produce la cláusula falsificada solo por la asignación \(a\).

Sin pérdida de generalidad, \(U=(z_0)\) (el otro caso es simétrico), así \(\chi=1\).

- Las cláusulas con \(a_0=0\) contienen el literal \(z_0\) y quedan satisfechas por \(z_0=1\); no se usan.
- Las cláusulas con \(a_0=1\) contienen \(\neg z_0\). Al resolver con \((z_0)\) se elimina \(\neg z_0\) y queda la cláusula del patrón \((a_1,\ldots,a_{d-1})\).

La condición \(1+\sum_{i\ge 1}a_i\not\equiv b\) es \(\sum_{i\ge 1}a_i\not\equiv b\oplus 1\).  
Esas son precisamente las cláusulas de \(\bigoplus_{i\ge 1}z_i=b\oplus 1\). \(\square\)

*(Implementado en `derive` / `_derive_by_unit`.)*

---

## Teorema C (árboles): \(\mathrm{Width}(T(T,c))=\Delta(T)\)

**Hipótesis.** \(T\) es un árbol con \(|V|\ge 1\), \(\sum c\) impar.

**Conclusión.** \(\mathrm{Width}(T(T,c))=\Delta(T)\).

### Prueba

La desigualdad \(\ge\) es el Corolario del Teorema A.

Para \(\le\), construimos una refutación de ancho \(\le\Delta\) por inducción en \(n=|V|\).

**Caso \(n=1\).** El único vértice tiene carga 1 y grado 0. La ecuación \(\bigoplus\emptyset=1\) es la cláusula vacía. Ancho \(0=\Delta\).

**Caso \(n=2\).** Hay una sola arista \(e=\{u,\ell\}\). Las dos restricciones de grado 1 son unidades sobre \(x_e\). Como la suma de cargas es impar, las unidades son opuestas: \((x_e)\) y \((\neg x_e)\). Su resolvente es \(\bot\). Ancho \(1=\Delta\).

**Caso \(n\ge 3\).** Sea \(\ell\) una hoja unida por \(e=\{\ell,u\}\), y sea \(\chi=c(\ell)\).  
La restricción en \(\ell\) es la unidad \(U\) que fija \(x_e=\chi\).

Sea \(T'=T-\ell\), y defínase \(c'(u)=c(u)\oplus\chi\) y \(c'(w)=c(w)\) si \(w\ne u\).  
Entonces \(\sum c'\) sigue siendo impar y \(T'\) es un árbol.

Por el Lema B, desde los axiomas de \(u\) en \(T\) y la unidad \(U\), se derivan (con resolución de ancho \(\le\deg_T(u)\le\Delta\)) exactamente los axiomas de la restricción de \(u\) en \(T(T',c')\). Los axiomas de los demás vértices de \(T'\) ya están en \(T(T,c)\).

Por hipótesis inductiva, \(T(T',c')\) tiene una refutación de ancho \(\le\Delta(T')\le\Delta(T)\).  
Componiendo: primero derivamos los axiomas de \(T'\) como arriba, luego simulamos esa refutación. El ancho global es \(\le\Delta(T)\). \(\square\)

**Certificado máquina:** `build_tree_tseitin_refutation` elimina hojas en el mismo orden y, cuando quedan dos vértices, resuelve las unidades conflictivas; `verify_resolution_derivation` comprueba cada paso.

---

## Teorema D (ciclos): \(\mathrm{Width}(T(C_n,c))=2\)

**Hipótesis.** \(C_n\) ciclo, \(n\ge 3\), \(\sum c\) impar. Entonces \(\Delta=2\).

**Conclusión.** \(\mathrm{Width}=2\).

### Prueba

\(\ge 2\) por el Teorema A.  

\(\le 2\): los axiomas tienen anchura \(\le 2\). El algoritmo de saturación de Ben-Sasson–Wigderson a ancho \(2\) termina con \(\bot\) porque la fórmula es insatisfacible y, para sistemas de 2-XOR en un ciclo con paridad impar, existe refutación de ancho 2 (composición de bicondicionales / eliminación gaussiana a lo largo del ciclo).  

Exhibimos un certificado explícito: saturación a ancho 2 registrando padres; verificado por `verify_resolution_derivation`. \(\square\)

---

## Lo que no hacemos

- No afirmamos novedad histórica del Teorema C (puede ser folklórico).  
- No extendemos a grafos con ciclos + árboles de forma general aquí (los 3-regulares ya muestran Width > Δ).  
- No hay afirmación sobre P vs NP.
