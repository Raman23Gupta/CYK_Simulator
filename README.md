# CYK Algorithm Simulator

An interactive web-based simulator for the **CYK (Cocke–Younger–Kasami) Algorithm**, used to determine whether a given string belongs to a **Context-Free Grammar (CFG)** in **Chomsky Normal Form (CNF)**.

---

## 🚀 Features

- 📥 Input custom Context-Free Grammar  
- 🔤 Input any string for validation  
- 📊 Step-by-step CYK table construction  
- 🎯 Final result: **Accepted / Rejected**  
- 🧠 Shows how variables derive substrings  
- 🎨 Clean and responsive **light-themed UI**

---

## 🧠 Concepts Covered

- Context-Free Grammars (CFG)  
- Chomsky Normal Form (CNF)  
- CYK Algorithm (Dynamic Programming)  
- Formal Language Parsing  

---

## 🛠️ Tech Stack

- HTML  
- CSS  
- JavaScript

---

## 📌 How It Works

1. Enter a grammar in CNF format:
```
S -> AB | BC
A -> BA | a
B -> CC | b
C -> AB | a
```

2. Enter an input string:
```
baaba
```

3. Click **"Run CYK"**

4. The simulator:
- Builds a triangular CYK table  
- Fills it step-by-step using dynamic programming  
- Computes variables that derive substrings  

5. Final result:
- ✅ Accepted (if the start symbol `S` is in the top cell)  
- ❌ Rejected (otherwise)

---

## 🌐 Live Demo

👉 [https://cyk-simulator-one.vercel.app](https://cyk-simulator-one.vercel.app)

---

## 🎓 Academic Context

This project was developed as part of a **Theory of Computation** course to demonstrate parsing using the CYK algorithm.

---

## 👨‍💻 Author

- Raman Gupta
- https://github.com/Raman23Gupta
