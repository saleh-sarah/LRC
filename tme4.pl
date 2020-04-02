/* Sarah Saleh
Lenaïg Tasso */

/*Exercice 1*/

subs(chat, felin).
subs(lion, felin).
subs(chien, canide).
subs(canide, chien).
subs(souris, mam).
subs(felin, mam).
subs(canide, mam).
subs(mam, animal).
subs(canari, animal).
subs(animal, etreVivant).
subs(and(animal, plante), nothing).

subs(pet, all(aMaitre,animal)). /*Un animal qui a un maitre est un animal de compagnie*/
subs(pet, some(aMaitre)).
subs(some(aMaitre),humain).
subs(chihuahua, chien).
subs(chihuahua, pet).

subs(animal, some(mange)). /*Tout animal se nourrit*/
subs(and(some(mange), all(mange,nothing)),nothing).

subs(lion, carnivoreExc).
subs(carnivoreExc,predateur).
     
equiv(carnivoreExc,all(mange,animal)).
equiv(herbivoreExc, all(mange,plante)).

inst(felix, chat).
inst(pierre,humain).
inst(princesse,chihuahua).
inst(marie, humain).
inst(jerry, souris).
inst(titi, canari).

instR(felix, aMaitre, pierre).
instR(princesse, aMaitre, marie).
instR(felix, mange, titi).
instR(felix,mange,jerry).

/*Exercice 2*/

/*1. Ces règles traduisent la transitivité.*/

subsS1(C,C).
subsS1(C,D) :- subs(C,D), C\==D.
subsS1(C,D) :- subs(C,E), subsS1(E,D).

/*2.

subsS1(canari, animal).
   Call: (7) subsS1(canari, animal) ? creep
   Call: (8) subs(canari, animal) ? creep
   Exit: (8) subs(canari, animal) ? creep
   Call: (8) canari\==animal ? creep
   Exit: (8) canari\==animal ? creep
   Exit: (7) subsS1(canari, animal) ? creep
true ;


subsS1(chat, etreVivant).
   Call: (7) subsS1(chat, etreVivant) ? creep
   Call: (8) subs(chat, etreVivant) ? creep
   Fail: (8) subs(chat, etreVivant) ? creep
   Redo: (7) subsS1(chat, etreVivant) ? creep
   Call: (8) subs(chat, _G1305) ? creep
   Exit: (8) subs(chat, felin) ? creep
   Call: (8) subsS1(felin, etreVivant) ? creep
   Call: (9) subs(felin, etreVivant) ? creep
   Fail: (9) subs(felin, etreVivant) ? creep
   Redo: (8) subsS1(felin, etreVivant) ? creep
   Call: (9) subs(felin, _G1305) ? creep
   Exit: (9) subs(felin, mam) ? creep
   Call: (9) subsS1(mam, etreVivant) ? creep
   Call: (10) subs(mam, etreVivant) ? creep
   Fail: (10) subs(mam, etreVivant) ? creep
   Redo: (9) subsS1(mam, etreVivant) ? creep
   Call: (10) subs(mam, _G1305) ? creep
   Exit: (10) subs(mam, animal) ? creep
   Call: (10) subsS1(animal, etreVivant) ? creep
   Call: (11) subs(animal, etreVivant) ? creep
   Exit: (11) subs(animal, etreVivant) ? creep
   Call: (11) animal\==etreVivant ? creep
   Exit: (11) animal\==etreVivant ? creep
   Exit: (10) subsS1(animal, etreVivant) ? creep
   Exit: (9) subsS1(mam, etreVivant) ? creep
   Exit: (8) subsS1(felin, etreVivant) ? creep
   Exit: (7) subsS1(chat, etreVivant) ? creep
true .

3.

subsS1(chien, souris).
   Call: (7) subsS1(chien, souris) ? creep
   Call: (8) subs(chien, souris) ? creep
   Fail: (8) subs(chien, souris) ? creep
   Redo: (7) subsS1(chien, souris) ? creep
   Call: (8) subs(chien, _G1305) ? creep
   Exit: (8) subs(chien, canide) ? creep
   Call: (8) subsS1(canide, souris) ? creep
   Call: (9) subs(canide, souris) ? creep
   Fail: (9) subs(canide, souris) ? creep
   Redo: (8) subsS1(canide, souris) ? creep
   Call: (9) subs(canide, _G1305) ? creep
   Exit: (9) subs(canide, chien) ? creep
   Call: (9) subsS1(chien, souris) ? creep
   Call: (10) subs(chien, souris) ? creep
   Fail: (10) subs(chien, souris) ? creep
   Redo: (9) subsS1(chien, souris) ? creep
   Call: (10) subs(chien, _G1305) ? creep
   Exit: (10) subs(chien, canide) ? creep
   Call: (10) subsS1(canide, souris) ? creep
   Call: (11) subs(canide, souris) ? creep
   Fail: (11) subs(canide, souris) ? creep
   Redo: (10) subsS1(canide, souris) ? creep

Cette requete part en boucle infinie car chien subsume canide et canide subsume chien.*/

/*4.*/

subsS(C,D) :- subsS(C,D,[C]).
subsS(C,C,_).
subsS(C,D,_) :- subs(C,D), C\==D.
subsS(C,D,L) :- subs(C,E),not(member(E,L)), subsS(E,D,[E|L]), E\==D.

/*
subsS(canari, animal).
   Call: (7) subsS(canari, animal) ? creep
   Call: (8) subsS(canari, animal, [canari]) ? creep
   Call: (9) subs(canari, animal) ? creep
   Exit: (9) subs(canari, animal) ? creep
   Call: (9) canari\==animal ? creep
   Exit: (9) canari\==animal ? creep
   Exit: (8) subsS(canari, animal, [canari]) ? creep
   Exit: (7) subsS(canari, animal) ? creep
true 


subsS(chat, etreVivant).
   Call: (7) subsS(chat, etreVivant) ? creep
   Call: (8) subsS(chat, etreVivant, [chat]) ? creep
   Call: (9) subs(chat, etreVivant) ? creep
   Fail: (9) subs(chat, etreVivant) ? creep
   Redo: (8) subsS(chat, etreVivant, [chat]) ? creep
   Call: (9) subs(chat, _G3088) ? creep
   Exit: (9) subs(chat, felin) ? creep
^  Call: (9) not(member(felin, [chat])) ? creep
^  Exit: (9) not(user:member(felin, [chat])) ? creep
   Call: (9) subsS(felin, etreVivant, [felin, chat]) ? creep
   Call: (10) subs(felin, etreVivant) ? creep
   Fail: (10) subs(felin, etreVivant) ? creep
   Redo: (9) subsS(felin, etreVivant, [felin, chat]) ? creep
   Call: (10) subs(felin, _G3097) ? creep
   Exit: (10) subs(felin, mam) ? creep
^  Call: (10) not(member(mam, [felin, chat])) ? creep
^  Exit: (10) not(user:member(mam, [felin, chat])) ? creep
   Call: (10) subsS(mam, etreVivant, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, etreVivant) ? creep
   Fail: (11) subs(mam, etreVivant) ? creep
   Redo: (10) subsS(mam, etreVivant, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, _G3106) ? creep
   Exit: (11) subs(mam, animal) ? creep
^  Call: (11) not(member(animal, [mam, felin, chat])) ? creep
^  Exit: (11) not(user:member(animal, [mam, felin, chat])) ? creep
   Call: (11) subsS(animal, etreVivant, [animal, mam, felin, chat]) ? creep
   Call: (12) subs(animal, etreVivant) ? creep
   Exit: (12) subs(animal, etreVivant) ? creep
   Call: (12) animal\==etreVivant ? creep
   Exit: (12) animal\==etreVivant ? creep
   Exit: (11) subsS(animal, etreVivant, [animal, mam, felin, chat]) ? creep
   Call: (11) animal\==etreVivant ? creep
   Exit: (11) animal\==etreVivant ? creep
   Exit: (10) subsS(mam, etreVivant, [mam, felin, chat]) ? creep
   Call: (10) mam\==etreVivant ? creep
   Exit: (10) mam\==etreVivant ? creep
   Exit: (9) subsS(felin, etreVivant, [felin, chat]) ? creep
   Call: (9) felin\==etreVivant ? creep
   Exit: (9) felin\==etreVivant ? creep
   Exit: (8) subsS(chat, etreVivant, [chat]) ? creep
   Exit: (7) subsS(chat, etreVivant) ? creep
true .


subsS(chien, canide).
   Call: (7) subsS(chien, canide) ? creep
   Call: (8) subsS(chien, canide, [chien]) ? creep
   Call: (9) subs(chien, canide) ? creep
   Exit: (9) subs(chien, canide) ? creep
   Call: (9) chien\==canide ? creep
   Exit: (9) chien\==canide ? creep
   Exit: (8) subsS(chien, canide, [chien]) ? creep
   Exit: (7) subsS(chien, canide) ? creep
true .

subsS(chien,chien).
   Call: (7) subsS(chien, chien) ? creep
   Call: (8) subsS(chien, chien, [chien]) ? creep
   Exit: (8) subsS(chien, chien, [chien]) ? creep
   Exit: (7) subsS(chien, chien) ? creep
true .


5.

subsS(souris, some(mange)).
   Call: (7) subsS(souris, some(mange)) ? creep
   Call: (8) subsS(souris, some(mange), [souris]) ? creep
   Call: (9) subs(souris, some(mange)) ? creep
   Fail: (9) subs(souris, some(mange)) ? creep
   Redo: (8) subsS(souris, some(mange), [souris]) ? creep
   Call: (9) subs(souris, _G3971) ? creep
   Exit: (9) subs(souris, mam) ? creep
^  Call: (9) not(member(mam, [souris])) ? creep
^  Exit: (9) not(user:member(mam, [souris])) ? creep
   Call: (9) subsS(mam, some(mange), [mam, souris]) ? creep
   Call: (10) subs(mam, some(mange)) ? creep
   Fail: (10) subs(mam, some(mange)) ? creep
   Redo: (9) subsS(mam, some(mange), [mam, souris]) ? creep
   Call: (10) subs(mam, _G3980) ? creep
   Exit: (10) subs(mam, animal) ? creep
^  Call: (10) not(member(animal, [mam, souris])) ? creep
^  Exit: (10) not(user:member(animal, [mam, souris])) ? creep
   Call: (10) subsS(animal, some(mange), [animal, mam, souris]) ? creep
   Call: (11) subs(animal, some(mange)) ? creep
   Exit: (11) subs(animal, some(mange)) ? creep
   Call: (11) animal\==some(mange) ? creep
   Exit: (11) animal\==some(mange) ? creep
   Exit: (10) subsS(animal, some(mange), [animal, mam, souris]) ? creep
   Call: (10) animal\==some(mange) ? creep
   Exit: (10) animal\==some(mange) ? creep
   Exit: (9) subsS(mam, some(mange), [mam, souris]) ? creep
   Call: (9) mam\==some(mange) ? creep
   Exit: (9) mam\==some(mange) ? creep
   Exit: (8) subsS(souris, some(mange), [souris]) ? creep
   Exit: (7) subsS(souris, some(mange)) ? creep
true .

6.


subsS(chat,humain).
   Call: (7) subsS(chat, humain) ? creep
   Call: (8) subsS(chat, humain, [chat]) ? creep
   Call: (9) subs(chat, humain) ? creep
   Fail: (9) subs(chat, humain) ? creep
   Redo: (8) subsS(chat, humain, [chat]) ? creep
   Call: (9) subs(chat, _G3967) ? creep
   Exit: (9) subs(chat, felin) ? creep
^  Call: (9) not(member(felin, [chat])) ? creep
^  Exit: (9) not(user:member(felin, [chat])) ? creep
   Call: (9) subsS(felin, humain, [felin, chat]) ? creep
   Call: (10) subs(felin, humain) ? creep
   Fail: (10) subs(felin, humain) ? creep
   Redo: (9) subsS(felin, humain, [felin, chat]) ? creep
   Call: (10) subs(felin, _G3976) ? creep
   Exit: (10) subs(felin, mam) ? creep
^  Call: (10) not(member(mam, [felin, chat])) ? creep
^  Exit: (10) not(user:member(mam, [felin, chat])) ? creep
   Call: (10) subsS(mam, humain, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, humain) ? creep
   Fail: (11) subs(mam, humain) ? creep
   Redo: (10) subsS(mam, humain, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, _G3985) ? creep
   Exit: (11) subs(mam, animal) ? creep
^  Call: (11) not(member(animal, [mam, felin, chat])) ? creep
^  Exit: (11) not(user:member(animal, [mam, felin, chat])) ? creep
   Call: (11) subsS(animal, humain, [animal, mam, felin, chat]) ? creep
   Call: (12) subs(animal, humain) ? creep
   Fail: (12) subs(animal, humain) ? creep
   Redo: (11) subsS(animal, humain, [animal, mam, felin, chat]) ? creep
   Call: (12) subs(animal, _G3994) ? creep
   Exit: (12) subs(animal, etreVivant) ? creep
^  Call: (12) not(member(etreVivant, [animal, mam, felin, chat])) ? creep
^  Exit: (12) not(user:member(etreVivant, [animal, mam, felin, chat])) ? creep
   Call: (12) subsS(etreVivant, humain, [etreVivant, animal, mam, felin, chat]) ? creep
   Call: (13) subs(etreVivant, humain) ? creep
   Fail: (13) subs(etreVivant, humain) ? creep
   Redo: (12) subsS(etreVivant, humain, [etreVivant, animal, mam, felin, chat]) ? creep
   Call: (13) subs(etreVivant, _G4003) ? creep
   Fail: (13) subs(etreVivant, _G4003) ? creep
   Fail: (12) subsS(etreVivant, humain, [etreVivant, animal, mam, felin, chat]) ? creep
   Redo: (12) subs(animal, _G3994) ? creep
   Exit: (12) subs(animal, some(mange)) ? creep
^  Call: (12) not(member(some(mange), [animal, mam, felin, chat])) ? creep
^  Exit: (12) not(user:member(some(mange), [animal, mam, felin, chat])) ? creep
   Call: (12) subsS(some(mange), humain, [some(mange), animal, mam, felin, chat]) ? creep
   Call: (13) subs(some(mange), humain) ? creep
   Fail: (13) subs(some(mange), humain) ? creep
   Redo: (12) subsS(some(mange), humain, [some(mange), animal, mam, felin, chat]) ? creep
   Call: (13) subs(some(mange), _G4005) ? creep
   Fail: (13) subs(some(mange), _G4005) ? creep
   Fail: (12) subsS(some(mange), humain, [some(mange), animal, mam, felin, chat]) ? creep
   Fail: (11) subsS(animal, humain, [animal, mam, felin, chat]) ? creep
   Fail: (10) subsS(mam, humain, [mam, felin, chat]) ? creep
   Fail: (9) subsS(felin, humain, [felin, chat]) ? creep
   Fail: (8) subsS(chat, humain, [chat]) ? creep
   Fail: (7) subsS(chat, humain) ? creep
false.

subsS(chien, souris).
   Call: (7) subsS(chien, souris) ? creep
   Call: (8) subsS(chien, souris, [chien]) ? creep
   Call: (9) subs(chien, souris) ? creep
   Fail: (9) subs(chien, souris) ? creep
   Redo: (8) subsS(chien, souris, [chien]) ? creep
   Call: (9) subs(chien, _G3997) ? creep
   Exit: (9) subs(chien, canide) ? creep
^  Call: (9) not(member(canide, [chien])) ? creep
^  Exit: (9) not(user:member(canide, [chien])) ? creep
   Call: (9) subsS(canide, souris, [canide, chien]) ? creep
   Call: (10) subs(canide, souris) ? creep
   Fail: (10) subs(canide, souris) ? creep
   Redo: (9) subsS(canide, souris, [canide, chien]) ? creep
   Call: (10) subs(canide, _G4006) ? creep
   Exit: (10) subs(canide, chien) ? creep
^  Call: (10) not(member(chien, [canide, chien])) ? creep
^  Fail: (10) not(user:member(chien, [canide, chien])) ? creep
   Redo: (10) subs(canide, _G4006) ? creep
   Exit: (10) subs(canide, mam) ? creep
^  Call: (10) not(member(mam, [canide, chien])) ? creep
^  Exit: (10) not(user:member(mam, [canide, chien])) ? creep
   Call: (10) subsS(mam, souris, [mam, canide, chien]) ? creep
   Call: (11) subs(mam, souris) ? creep
   Fail: (11) subs(mam, souris) ? creep
   Redo: (10) subsS(mam, souris, [mam, canide, chien]) ? creep
   Call: (11) subs(mam, _G4015) ? creep
   Exit: (11) subs(mam, animal) ? creep
^  Call: (11) not(member(animal, [mam, canide, chien])) ? creep
^  Exit: (11) not(user:member(animal, [mam, canide, chien])) ? creep
   Call: (11) subsS(animal, souris, [animal, mam, canide, chien]) ? creep
   Call: (12) subs(animal, souris) ? creep
   Fail: (12) subs(animal, souris) ? creep
   Redo: (11) subsS(animal, souris, [animal, mam, canide, chien]) ? creep
   Call: (12) subs(animal, _G4024) ? creep
   Exit: (12) subs(animal, etreVivant) ? creep
^  Call: (12) not(member(etreVivant, [animal, mam, canide, chien])) ? creep
^  Exit: (12) not(user:member(etreVivant, [animal, mam, canide, chien])) ? creep
   Call: (12) subsS(etreVivant, souris, [etreVivant, animal, mam, canide, chien]) ? creep
   Call: (13) subs(etreVivant, souris) ? creep
   Fail: (13) subs(etreVivant, souris) ? creep
   Redo: (12) subsS(etreVivant, souris, [etreVivant, animal, mam, canide, chien]) ? creep
   Call: (13) subs(etreVivant, _G4033) ? creep
   Fail: (13) subs(etreVivant, _G4033) ? creep
   Fail: (12) subsS(etreVivant, souris, [etreVivant, animal, mam, canide, chien]) ? creep
   Redo: (12) subs(animal, _G4024) ? creep
   Exit: (12) subs(animal, some(mange)) ? creep
^  Call: (12) not(member(some(mange), [animal, mam, canide, chien])) ? creep
^  Exit: (12) not(user:member(some(mange), [animal, mam, canide, chien])) ? creep
   Call: (12) subsS(some(mange), souris, [some(mange), animal, mam, canide, chien]) ? creep
   Call: (13) subs(some(mange), souris) ? creep
   Fail: (13) subs(some(mange), souris) ? creep
   Redo: (12) subsS(some(mange), souris, [some(mange), animal, mam, canide, chien]) ? creep
   Call: (13) subs(some(mange), _G4035) ? creep
   Fail: (13) subs(some(mange), _G4035) ? creep
   Fail: (12) subsS(some(mange), souris, [some(mange), animal, mam, canide, chien]) ? creep
   Fail: (11) subsS(animal, souris, [animal, mam, canide, chien]) ? creep
   Fail: (10) subsS(mam, souris, [mam, canide, chien]) ? creep
   Fail: (9) subsS(canide, souris, [canide, chien]) ? creep
   Fail: (8) subsS(chien, souris, [chien]) ? creep
   Fail: (7) subsS(chien, souris) ? creep
false.


7. La requete subsS(chat,X) devrait renvoyer X=chat, felin, animal, mam, etreVivant et some(mange).
La requete subsS(X,mam) devrait renvoyer X=felin,souris, canide,chien,chat ,lion, chihuahua.

subsS(chat,X).
   Call: (7) subsS(chat, _G4746) ? creep
   Call: (8) subsS(chat, _G4746, [chat]) ? creep
   Exit: (8) subsS(chat, chat, [chat]) ? creep
   Exit: (7) subsS(chat, chat) ? creep
X = chat ;
   Redo: (8) subsS(chat, _G4746, [chat]) ? creep
   Call: (9) subs(chat, _G4746) ? creep
   Exit: (9) subs(chat, felin) ? creep
   Call: (9) chat\==felin ? creep
   Exit: (9) chat\==felin ? creep
   Exit: (8) subsS(chat, felin, [chat]) ? creep
   Exit: (7) subsS(chat, felin) ? creep
X = felin ;
   Redo: (8) subsS(chat, _G4746, [chat]) ? creep
   Call: (9) subs(chat, _G4828) ? creep
   Exit: (9) subs(chat, felin) ? creep
^  Call: (9) not(member(felin, [chat])) ? creep
^  Exit: (9) not(user:member(felin, [chat])) ? creep
   Call: (9) subsS(felin, _G4746, [felin, chat]) ? creep
   Exit: (9) subsS(felin, felin, [felin, chat]) ? creep
   Call: (9) felin\==felin ? creep
   Fail: (9) felin\==felin ? creep
   Redo: (9) subsS(felin, _G4746, [felin, chat]) ? creep
   Call: (10) subs(felin, _G4746) ? creep
   Exit: (10) subs(felin, mam) ? creep
   Call: (10) felin\==mam ? creep
   Exit: (10) felin\==mam ? creep
   Exit: (9) subsS(felin, mam, [felin, chat]) ? creep
   Call: (9) felin\==mam ? creep
   Exit: (9) felin\==mam ? creep
   Exit: (8) subsS(chat, mam, [chat]) ? creep
   Exit: (7) subsS(chat, mam) ? creep
X = mam ;
   Redo: (9) subsS(felin, _G4746, [felin, chat]) ? creep
   Call: (10) subs(felin, _G4837) ? creep
   Exit: (10) subs(felin, mam) ? creep
^  Call: (10) not(member(mam, [felin, chat])) ? creep
^  Exit: (10) not(user:member(mam, [felin, chat])) ? creep
   Call: (10) subsS(mam, _G4746, [mam, felin, chat]) ? creep
   Exit: (10) subsS(mam, mam, [mam, felin, chat]) ? creep
   Call: (10) mam\==mam ? creep
   Fail: (10) mam\==mam ? creep
   Redo: (10) subsS(mam, _G4746, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, _G4746) ? creep
   Exit: (11) subs(mam, animal) ? creep
   Call: (11) mam\==animal ? creep
   Exit: (11) mam\==animal ? creep
   Exit: (10) subsS(mam, animal, [mam, felin, chat]) ? creep
   Call: (10) mam\==animal ? creep
   Exit: (10) mam\==animal ? creep
   Exit: (9) subsS(felin, animal, [felin, chat]) ? creep
   Call: (9) felin\==animal ? creep
   Exit: (9) felin\==animal ? creep
   Exit: (8) subsS(chat, animal, [chat]) ? creep
   Exit: (7) subsS(chat, animal) ? creep
X = animal ;
   Redo: (10) subsS(mam, _G4746, [mam, felin, chat]) ? creep
   Call: (11) subs(mam, _G4846) ? creep
   Exit: (11) subs(mam, animal) ? creep
^  Call: (11) not(member(animal, [mam, felin, chat])) ? creep
^  Exit: (11) not(user:member(animal, [mam, felin, chat])) ? creep
   Call: (11) subsS(animal, _G4746, [animal, mam, felin, chat]) ? creep
   Exit: (11) subsS(animal, animal, [animal, mam, felin, chat]) ? creep
   Call: (11) animal\==animal ? creep
   Fail: (11) animal\==animal ? creep
   Redo: (11) subsS(animal, _G4746, [animal, mam, felin, chat]) ? creep
   Call: (12) subs(animal, _G4746) ? creep
   Exit: (12) subs(animal, etreVivant) ? creep
   Call: (12) animal\==etreVivant ? creep
   Exit: (12) animal\==etreVivant ? creep
   Exit: (11) subsS(animal, etreVivant, [animal, mam, felin, chat]) ? creep
   Call: (11) animal\==etreVivant ? creep
   Exit: (11) animal\==etreVivant ? creep
   Exit: (10) subsS(mam, etreVivant, [mam, felin, chat]) ? creep
   Call: (10) mam\==etreVivant ? creep
   Exit: (10) mam\==etreVivant ? creep
   Exit: (9) subsS(felin, etreVivant, [felin, chat]) ? creep
   Call: (9) felin\==etreVivant ? creep
   Exit: (9) felin\==etreVivant ? creep
   Exit: (8) subsS(chat, etreVivant, [chat]) ? creep
   Exit: (7) subsS(chat, etreVivant) ? creep
X = etreVivant ;
   Redo: (12) subs(animal, _G4746) ? creep
   Exit: (12) subs(animal, some(mange)) ? creep
   Call: (12) animal\==some(mange) ? creep
   Exit: (12) animal\==some(mange) ? creep
   Exit: (11) subsS(animal, some(mange), [animal, mam, felin, chat]) ? creep
   Call: (11) animal\==some(mange) ? creep
   Exit: (11) animal\==some(mange) ? creep
   Exit: (10) subsS(mam, some(mange), [mam, felin, chat]) ? creep
   Call: (10) mam\==some(mange) ? creep
   Exit: (10) mam\==some(mange) ? creep
   Exit: (9) subsS(felin, some(mange), [felin, chat]) ? creep
   Call: (9) felin\==some(mange) ? creep
   Exit: (9) felin\==some(mange) ? creep
   Exit: (8) subsS(chat, some(mange), [chat]) ? creep
   Exit: (7) subsS(chat, some(mange)) ? creep
X = some(mange) ;
   Redo: (11) subsS(animal, _G4746, [animal, mam, felin, chat]) ? creep
   Call: (12) subs(animal, _G4855) ? creep
   Exit: (12) subs(animal, etreVivant) ? creep
^  Call: (12) not(member(etreVivant, [animal, mam, felin, chat])) ? creep
^  Exit: (12) not(user:member(etreVivant, [animal, mam, felin, chat])) ? creep
   Call: (12) subsS(etreVivant, _G4746, [etreVivant, animal, mam, felin, chat]) ? creep
   Exit: (12) subsS(etreVivant, etreVivant, [etreVivant, animal, mam, felin, chat]) ? creep
   Call: (12) etreVivant\==etreVivant ? creep
   Fail: (12) etreVivant\==etreVivant ? creep
   Redo: (12) subsS(etreVivant, _G4746, [etreVivant, animal, mam, felin, chat]) ? creep
   Call: (13) subs(etreVivant, _G4746) ? creep
   Fail: (13) subs(etreVivant, _G4746) ? creep
   Redo: (12) subsS(etreVivant, _G4746, [etreVivant, animal, mam, felin, chat]) ? creep
   Call: (13) subs(etreVivant, _G4864) ? creep
   Fail: (13) subs(etreVivant, _G4864) ? creep
   Fail: (12) subsS(etreVivant, _G4746, [etreVivant, animal, mam, felin, chat]) ? creep
   Redo: (12) subs(animal, _G4855) ? creep
   Exit: (12) subs(animal, some(mange)) ? creep
^  Call: (12) not(member(some(mange), [animal, mam, felin, chat])) ? creep
^  Exit: (12) not(user:member(some(mange), [animal, mam, felin, chat])) ? creep
   Call: (12) subsS(some(mange), _G4746, [some(mange), animal, mam, felin, chat]) ? creep
   Exit: (12) subsS(some(mange), some(mange), [some(mange), animal, mam, felin, chat]) ? creep
   Call: (12) some(mange)\==some(mange) ? creep
   Fail: (12) some(mange)\==some(mange) ? creep
   Redo: (12) subsS(some(mange), _G4746, [some(mange), animal, mam, felin, chat]) ? creep
   Call: (13) subs(some(mange), _G4746) ? creep
   Fail: (13) subs(some(mange), _G4746) ? creep
   Redo: (12) subsS(some(mange), _G4746, [some(mange), animal, mam, felin, chat]) ? creep
   Call: (13) subs(some(mange), _G4866) ? creep
   Fail: (13) subs(some(mange), _G4866) ? creep
   Fail: (12) subsS(some(mange), _G4746, [some(mange), animal, mam, felin, chat]) ? creep
   Fail: (11) subsS(animal, _G4746, [animal, mam, felin, chat]) ? creep
   Fail: (10) subsS(mam, _G4746, [mam, felin, chat]) ? creep
   Fail: (9) subsS(felin, _G4746, [felin, chat]) ? creep
   Fail: (8) subsS(chat, _G4746, [chat]) ? creep
   Fail: (7) subsS(chat, _G4746) ? creep
false.


subsS(X,mam) :
X = mam ;
X = souris ;
X = felin ;
X = canide ;
X = chat ;
X = lion ;
X = chien ;
X = chihuahua ;
false.

8.
*/

/*equiv1(A,B) :- subs(A,B), subs(B,A).*/

/*9.
subsS1(lion,all(mange,animal)).
false.

10.




Exercice 3


*/


subsS(C,and(D1,D2),L) :- D1\=D2,subsS(C,D1,L),subsS(C,D2,L).
subsS(C,D,L) :- subs(and(D1,D2),D),E=and(D1,D2),not(member(E,L)),subsS(C,E,[E|L]),E\==C.
subsS(and(C,C), D, L) :- nonvar(C), subsS(C,D,[C|L]).
subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C1, D, [C1 |L]).
subsS(and(C1,C2), D, L) :- C1\=C2, subsS(C2, D, [C2 |L]).
subsS(and(C1, C2),D,L) :- subs(C1, E1),E=and(E1,C2),not(member(E,L)),subsS(E,D,[E|L]),E\==D.
subsS(and(C1, C2),D,L) :- Cinv=and(C2,C1), not(member(Cinv, L)), subsS(Cinv,D,[Cinv|L]).

/* 
subsS(chihuahua, and(mam,some(aMaitre))).
true 

subsS(and(chien,some(aMaitre)),pet).
false.



subsS(chihuahua, and(pet,chien)).
true 


2.
subsS(C,and(D1,D2),L) :- D1\=D2,subsS(C,D1,L),subsS(C,D2,L).
Cette règle correspond au fait que si C est compris dans l'intersection de D1 et D2 alors C est compris dans D1 et C est compris dans D2.


