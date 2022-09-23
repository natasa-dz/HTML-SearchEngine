# -*- coding: utf-8 -*-
from contextlib import _GeneratorContextManager
import re
import os
import sys
import errno, os
import subprocess
# Sadly, Python fails to provide the following magic number for us.
ERROR_INVALID_NAME = 123
from collections import OrderedDict
from html.parser import HTMLParser
from typing import Tuple
from unittest import result

# from html.parser import ParsingError

"-------------------------------------        TRIE  AND TRIENODE        --------------------------------------------"
class TrieNode:
    def __init__(self, vrednost):
        self.vrednost = vrednost
        self.deca = {}
        self.kraj = False
        self.putanja = None
        self.susedi_elementa = []
        self.broj_pojavljivanja = 0

class Trie:
    def __init__(self):
        self.koren = TrieNode(None)

    # insert vrsi ubacivanje reci u trie
    # parent.file_path i surroundings-sluze da znamo gde se nalazimo u kom fajlu, i sta je nase okruzenje
    def insert(self, rec, putanja, susedi_elementa):

        roditelj = self.koren
        for i, char in enumerate(rec):
            if char not in roditelj.deca:
                roditelj.deca[char] = TrieNode(char)
            roditelj = roditelj.deca[char]
            if i == len(rec) - 1:
                roditelj.kraj = True

                roditelj.putanja = putanja

                roditelj.susedi_elementa.append(susedi_elementa)
                roditelj.broj_pojavljivanja += 1

    # search vrsi pronalazenje reci u Tries-u
    def search(self, rec):

        roditelj = self.koren
        for char in rec:
            if char not in roditelj.deca:
                return 0, []
            roditelj = roditelj.deca[char]
        return roditelj.broj_pojavljivanja, roditelj.susedi_elementa

    # funkcija koja nam sluzi da na osnovu unesenih par karaktera nadjemo sve reci koje sadrze upravo te karaktere
    def starts_with(self, prefix):
        roditelj = self.koren
        for karakter in prefix:
            if karakter not in roditelj.deca:
                return False
            roditelj = roditelj.deca[karakter]
        return True

"""---------------------------------------- GRAPH ---------------------------------------------"""
class Graph:
    """ Reprezentacija jednostavnog grafa"""

    # ------------------------- Ugnježdena klasa Vertex -------------------------
    class Vertex:
        """ Struktura koja predstavlja čvor grafa."""
        __slots__ = '_element'

        def __init__(self, x):
            self._element = x

        def element(self):
            """Vraća element vezan za čvor grafa."""
            return self._element

        def __hash__(self):  # omogućava da Vertex bude ključ mape
            return hash(id(self))

        def __str__(self):
            return str(self._element)

    # ------------------------- Ugnježdena klasa Edge -------------------------
    class Edge:
        """ Struktura koja predstavlja ivicu grafa """
        __slots__ = '_origin', '_destination', '_element'

        def __init__(self, origin, destination, element):
            self._origin = origin
            self._destination = destination
            self._element = element

        def endpoints(self):
            """ Vraća torku (u,v) za čvorove u i v."""
            return (self._origin, self._destination)

        def opposite(self, v):
            """ Vraća čvor koji se nalazi sa druge strane čvora v ove ivice."""
            if not isinstance(v, Graph.Vertex):
                raise TypeError('v mora biti instanca klase Vertex')
            if self._destination == v:
                return self._origin
            elif self._origin == v:
                return self._destination
            raise ValueError('v nije čvor ivice')

        def element(self):
            """ Vraća element vezan za ivicu"""
            return self._element

        def __hash__(self):  # omogućava da Edge bude ključ mape
            return hash((self._origin, self._destination))

        def __str__(self):
            return '({0},{1},{2})'.format(self._origin, self._destination, self._element)

    # ------------------------- Metode klase Graph -------------------------
    def __init__(self, directed=False):
        """ Kreira prazan graf (podrazumevana vrednost je da je neusmeren).

        Ukoliko se opcioni parametar directed postavi na True, kreira se usmereni graf.
        """
        self._outgoing = {}
        # ukoliko je graf usmeren, kreira se pomoćna mapa
        self._incoming = {} if directed else self._outgoing

    def _validate_vertex(self, v):
        """ Proverava da li je v čvor(Vertex) ovog grafa."""
        if not isinstance(v, self.Vertex):
            raise TypeError('Očekivan je objekat klase Vertex')
        if v not in self._outgoing:
            raise ValueError('Vertex ne pripada ovom grafu.')

    def is_directed(self):
        """ Vraća True ako je graf usmeren; False ako je neusmeren."""
        return self._incoming is not self._outgoing  # graf je usmeren ako se mape razlikuju

    def vertex_count(self):
        """ Vraća broj čvorova u grafu."""
        return len(self._outgoing)

    def vertices(self):
        """ Vraća iterator nad svim čvorovima grafa."""
        return self._outgoing.keys()

    def edge_count(self):
        """ Vraća broj ivica u grafu."""
        total = sum(len(self._outgoing[v]) for v in self._outgoing)
        # ukoliko je graf neusmeren, vodimo računa da ne brojimo čvorove više puta
        return total if self.is_directed() else total // 2

    def edges(self):
        """ Vraća set svih ivica u grafu."""
        result = set()  # pomoću seta osiguravamo da čvorove neusmerenog grafa brojimo samo jednom
        for secondary_map in self._outgoing.values():
            result.update(secondary_map.values())  # dodavanje ivice u rezultujući set
        return result

    def get_edge(self, u, v):
        """ Vraća ivicu između čvorova u i v ili None ako nisu susedni."""
        self._validate_vertex(u)
        self._validate_vertex(v)
        return self._outgoing[u].get(v)

    def degree(self, v, outgoing=True):
        """ Vraća stepen čvora - broj(odlaznih) ivica iz čvora v u grafu.

        Ako je graf usmeren, opcioni parametar outgoing se koristi za brojanje dolaznih ivica.
        """
        self._validate_vertex(v)
        adj = self._outgoing if outgoing else self._incoming
        return len(adj[v])

    def incident_edges(self, v, outgoing=True):
        """ Vraća sve (odlazne) ivice iz čvora v u grafu.

        Ako je graf usmeren, opcioni parametar outgoing se koristi za brojanje dolaznih ivica.
        """
        self._validate_vertex(v)
        adj = self._outgoing if outgoing else self._incoming
        for edge in adj[v].values():
            yield edge

    def insert_vertex(self, x=None):
        """ Ubacuje i vraća novi čvor (Vertex) sa elementom x"""
        v = self.Vertex(x)
        self._outgoing[v] = {}
        if self.is_directed():
            self._incoming[v] = {}  # mapa različitih vrednosti za dolazne čvorove
        return v

    def insert_edge(self, u, v, x=None):
        """ Ubacuje i vraća novu ivicu (Edge) od u do v sa pomoćnim elementom x.

        Baca ValueError ako u i v nisu čvorovi grafa.
        Baca ValueError ako su u i v već povezani.
        """
        if self.get_edge(u, v) is not None:  # uključuje i proveru greške
            raise ValueError('u and v are already adjacent')
        e = self.Edge(u, v, x)
        self._outgoing[u][v] = e
        self._incoming[v][u] = e

"""-------------------------------------------------    PARSER    --------------------------------------------------------"""
class ParsingError(Exception):
    pass

class Parser(HTMLParser):
    """
    Parser HTML dokumenata

    Upotreba:
        parser = Parser()
        parser.parse(FILE_PATH)
    """

    def handle_starttag(self, tag, attrs):
        """
        Metoda beleži sadržaj href atributa

        Poziv metode vrši se implicitno prilikom nailaska na tag
        unutar HTML fajla. Ukoliko je u pitanju anchor tag, beleži
        se vrednost href atributa.

        Argumenti:
        - `tag`: naziv taga
        - `attrs`: lista atributa
        """
        if tag == 'a':
            # typecast da izbegnem looping
            attrs = dict(attrs)
            link = attrs['href']

            # ignoriši spoljnje linkove i uzmi u obzir samo html fajlove
            if not link.startswith('http'):
                # ukloni sekciju iz linka
                hash_index = link.rfind('#')
                if hash_index > -1:
                    link = link[:hash_index]

                if link.endswith('html') or link.endswith('htm'):
                    relative_path = os.path.join(self.path_root, link)
                    link_path = os.path.abspath(relative_path)
                    self.links.append(link_path)

    def handle_data(self, data):
        """
        Metoda beleži pronađene reči

        Poziv metode vrši se implicitno prilikom nailaska na sadržaj
        HTML elemenata. Sadržaj elementa se deli u reči koje se beleže
        u odgovarajuću listu.

        Argument:
        - `data`: dobijeni sadržaj elementa
        """
        stripped_text = re.sub('[\W]', ' ', data).split()
        if stripped_text:
            self.words.extend(stripped_text)

    def error(self, message):
        raise ParsingError(message)

    def parse(self, path):
        """
        Metoda učitava sadržaj fajla i prosleđuje ga parseru

        Argument:
        - `path`: putanja do fajla
        """
        self.links = []
        self.words = []

        try:
            with open(path, 'r', encoding="UTF-8") as document:
                self.path_root = os.path.abspath(os.path.dirname(path))
                content = document.read()
                self.feed(content)

                # očisti duplikate
                self.links = list(set(self.links))

        except IOError as e:
            print(e)
        finally:
            return self.links, self.words

"""----------------------------------------- Meni -----------------------------------------"""
parser = Parser()

graf = Graph(directed=True)
pronadjene_reci = []
objekat_cvora = {}
recnik_linkova_fajla = {}


def odabir_korisnika():
    print("         DOBRODOSLI U TEKSTUALNI SEARCH ENGINE!         ")
    print("========================================================")
    print("[1] Pretrazivanje pomocu unosa reci i logickih operatera [AND, OR, NOT]")
    print("[2] Izlazak")
    print("==========================================================")
    print("")

    opcije = [1, 2]
    print("Izaberite opciju")
    odabir = input("--->")

    while odabir.strip() in str(opcije):
        if odabir.strip() == "1":
            AND_OR_NOT_pretrazivanje()

        elif odabir.strip() == "2":
            quit()
    print("Odabrali ste nepostojecu opciju, pokusajte ponovo sa validnim izborom!")
    print("")
    odabir_korisnika()

def dodaj_sadrzaj_u_listu(lista_pronadjenih_reci):
    for rec in lista_pronadjenih_reci:
        rec_lower = rec.lower()
        if rec_lower in pronadjene_reci:
            pass
        else:
            pronadjene_reci.append(rec_lower)

def nadji_ime_fajla(putanja_fajla):
    separator = os.path.sep
    putanja_fajla_splitovano = putanja_fajla.split(separator)
    ime_fajla = putanja_fajla_splitovano[-1]
    return ime_fajla

def formiraj_trie_pokusaj(lista_reci, ime_fajla, pozicija):
    trie = Trie()
    susedne_reci = []
    pozicija_reci = pozicija

    if pozicija_reci in range(len(lista_reci) - 24, len(lista_reci)):
        for rec in range(len(lista_reci) - 24, len(lista_reci)):
            susedne_reci.append(lista_reci[rec])

    else:
        for rec in range(pozicija_reci, pozicija_reci + 24):
            susedne_reci.append(lista_reci[rec])

    for pozicija in range(len(lista_reci)):
        if not lista_reci[pozicija]:
            continue
        trazena_rec = lista_reci[pozicija].lower()
        trie.insert(trazena_rec, ime_fajla, susedne_reci)

# prikazujemo dvadeset i cetiri susedne reci pored nase trazene reci-medjuostalom i pomocna funkcija prilikom prikaza isecka korisniku
def pronadji_susedne_reci(lista_reci, pozicija):
    susedne_reci = []
    pozicija_reci = pozicija

    if pozicija_reci in range(len(lista_reci) - 18, len(lista_reci)):
        for rec in range(len(lista_reci) - 18, len(lista_reci)):
            susedne_reci.append(lista_reci[rec])
        return susedne_reci

    else:
        for rec in range(pozicija_reci, pozicija_reci + 18):
            susedne_reci.append(lista_reci[rec])
        return susedne_reci

def formiraj_trie(lista_reci, ime_fajla):
    trie = Trie()
    for rec in range(len(lista_reci)):
        if not lista_reci[rec]:
            continue
        trazena_rec = lista_reci[rec].lower()
        susedne_reci = pronadji_susedne_reci(lista_reci, rec)
        trie.insert(trazena_rec, ime_fajla, susedne_reci)
    return trie

def pronadji_linkove_unutar_foldera(linkovi_foldera):
    separator = os.path.sep
    lista_linkova = []
    for link in linkovi_foldera:
        split_lilnk = link.split(separator)
        naziv_linka = split_lilnk[-1]
        if naziv_linka in lista_linkova:
            pass
        else:
            lista_linkova.append(naziv_linka)
    return lista_linkova

def listdirs(rootdir):
    for file in os.listdir(rootdir):
        d = os.path.join(rootdir, file)
        if os.path.isdir(d):
            print(d)
            listdirs(d)

# funkcija vrsi ucitavanje podataka i vraca nam potrebne podatke koji nam trebaju za Graph-edges, Vertex i stvara Trie za prosledjene reci
def ucitaj_fajlove(putanja_foldera):
    SEPARATOR = os.path.sep
    for naziv_fajl in os.listdir(putanja_foldera):

        if naziv_fajl.endswith("html"):

            putanja_fajla = putanja_foldera + SEPARATOR + naziv_fajl
            linkovi_unutar_foldera, lista_pronadjenih_reci = parser.parse(putanja_fajla)

            if not lista_pronadjenih_reci:
                continue

            # nalazi sve html fajlove u korenskom direktorijumu
            dodaj_sadrzaj_u_listu(lista_pronadjenih_reci)

            ime_fajla = nadji_ime_fajla(putanja_fajla)
            # print(ime_fajla)

            sadrzaj_foldera = pronadji_linkove_unutar_foldera(linkovi_unutar_foldera)
            # print("")
            # print("")
            # print(sadrzaj_foldera)
            # print("-----------------------------------------------------")

            recnik_linkova_fajla[ime_fajla] = sadrzaj_foldera

            # print(recnik_linkova_fajla)
            # print("-----------------------------------------------------")

            formiraj_trie_za_fajl = formiraj_trie(lista_pronadjenih_reci, ime_fajla)

            element_vertexa = {ime_fajla: formiraj_trie_za_fajl}
            vertex = graf.insert_vertex(element_vertexa)
            objekat_cvora[ime_fajla] = vertex
            """else:
            print("U datom direktorijumu ne postoji nijedan fajl html formata!")
            print("Pokusajte sa nekim mdrugim direktorijumom!")
            pokreni_pretrazivac()"""
        elif not os.path.isfile(putanja_foldera+SEPARATOR+naziv_fajl) and not (re.search("^.*.(js|JS|img|IMG|jpg|JPG|jpeg|JPEG|inv|INV|doc|DOC|pdf|PDF)$", naziv_fajl)):\
            ucitaj_fajlove(putanja_foldera+SEPARATOR+naziv_fajl)

#fajl, linkovi tog fajla, povezi ih sa cvorem
def ubaci_podatke_u_grane():
    for fajl in recnik_linkova_fajla.keys():
        for ime_linka in recnik_linkova_fajla[fajl]:
            if ime_linka in objekat_cvora:
                graf.insert_edge(objekat_cvora[fajl], objekat_cvora[ime_linka], ime_linka)

def NOT_pretraga_za_dva_kriterijuma(lista_kriterijuma):
    rezultati_za_kriterijum1 = []
    rezultati_za_kriterijum2 = []
    lista_fajlova = []
    pozicija = 0

    for rec in lista_kriterijuma:
        if rec==lista_kriterijuma[0]:
            pozicija=1
        elif rec==lista_kriterijuma[1]:
            pozicija=2

        for naziv_fajla in objekat_cvora:
            vertex_trie = objekat_cvora[naziv_fajla]._element[naziv_fajla]
            broj_pojavljivanja_trazene_reci, _ = vertex_trie.search(rec.lower())

            if broj_pojavljivanja_trazene_reci != 0 and pozicija == 1:
                rezultati_za_kriterijum1.append(naziv_fajla)

            elif broj_pojavljivanja_trazene_reci == 0 and pozicija == 2:
                rezultati_za_kriterijum2.append(naziv_fajla)

    for ime_fajla1 in rezultati_za_kriterijum1:
        for ime_fajla2 in rezultati_za_kriterijum2:
            if (ime_fajla1 == ime_fajla2) and (ime_fajla1 not in lista_fajlova):
                lista_fajlova.append(ime_fajla1)
    return lista_fajlova

def OR_pretraga_za_dva_kriterijuma(lista_kriterijuma):
    rezultati_za_kriterijum1 = []
    rezultati_za_kriterijum2 = []
    lista_fajlova = []
    pozicija = 0

    for rec in lista_kriterijuma:
        if rec==lista_kriterijuma[0]:
            pozicija=1
        elif rec==lista_kriterijuma[1]:
            pozicija=2

        for naziv_fajla in objekat_cvora:
            vertex_trie = objekat_cvora[naziv_fajla]._element[naziv_fajla]
            broj_pojavljivanja_trazene_reci, _ = vertex_trie.search(rec.lower())
            if pozicija == 1 and broj_pojavljivanja_trazene_reci != 0:
                rezultati_za_kriterijum1.append(naziv_fajla)
            elif pozicija == 2 and broj_pojavljivanja_trazene_reci != 0:
                rezultati_za_kriterijum2.append(naziv_fajla)

    for ime_fajla in rezultati_za_kriterijum1:
        if ime_fajla not in lista_fajlova:
            lista_fajlova.append(ime_fajla)

    for ime_fajla in rezultati_za_kriterijum2:
        if ime_fajla not in lista_fajlova:
            lista_fajlova.append(ime_fajla)

    return lista_fajlova

def AND_pretraga_za_dva_kriterijuma(lista_kriterijuma):
    rezultati_za_kriterijum1 = []
    rezultati_za_kriterijum2 = []
    konacan_rezultat = []
    pozicija_kriterijuma=0

    for rec in lista_kriterijuma:
        if rec==lista_kriterijuma[0]:
            pozicija_kriterijuma=1
        elif rec==lista_kriterijuma[1]:
            pozicija_kriterijuma=2
        for kljuc in objekat_cvora:

            trie_u_vertexu = objekat_cvora[kljuc]._element[kljuc]
            pojavljivanje_trazene_reci, _ = trie_u_vertexu.search(rec.lower())

            if pozicija_kriterijuma == 1 and pojavljivanje_trazene_reci != 0:
                rezultati_za_kriterijum1.append(kljuc)
            if pozicija_kriterijuma == 2 and pojavljivanje_trazene_reci != 0:
                rezultati_za_kriterijum2.append(kljuc)

    for ime_fajla1 in rezultati_za_kriterijum1:
        for ime_fajla2 in rezultati_za_kriterijum2:
            if (ime_fajla1 not in konacan_rezultat) and (ime_fajla2 == ime_fajla1):
                konacan_rezultat.append((ime_fajla1))
    return konacan_rezultat

def NOT_pretraga_za_vise_od_dva_kriterijuma(lista_svih_fajlova, rec):
    # lista fajlova u kojima se ne nalazi odabrana rec
    fajlovi_bez_reci = []
    # vracamo listu svih fajlova koji ne sadrze odredjenu rec
    lista_not_fajlova = []
    for kljuc in objekat_cvora:
        # pronalazimo sve reci nekog fajla i stavljamo fa u vertex
        stavi_trie_u_vertex = objekat_cvora[kljuc]._element[kljuc]
        # proveravamo da li se nalazi rec u trie-u u vertexu
        broj_ponavljanja, _ = stavi_trie_u_vertex.search(rec.lower())

        if broj_ponavljanja == 0:
            fajlovi_bez_reci.append(kljuc)

    for ime_fajla in fajlovi_bez_reci:
        if ime_fajla in lista_svih_fajlova:
            lista_not_fajlova.append(ime_fajla)
    return lista_not_fajlova

def AND_pretraga_za_vise_od_dva_kriterijuma(lista_svih_fajlova, rec):
    fajlovi_sa_recima = []
    # vracamo listu svih fajlova koji sadrze trazeni sadrzaj
    lista_AND_fajlova = []

    for ime_fajla_unutar_cvora in objekat_cvora:
        # pronalazimo sve reci nekog fajla i stavljamo fa u vertex
        stavi_trie_u_vertex = objekat_cvora[ime_fajla_unutar_cvora]._element[ime_fajla_unutar_cvora]
        # proveravamo da li se nalazi rec u trie-u u vertexu
        ponavljanje_trazene_reci, _ = stavi_trie_u_vertex.search(rec.lower())

        if ponavljanje_trazene_reci != 0:
            fajlovi_sa_recima.append(ime_fajla_unutar_cvora)

    for ime_fajla in fajlovi_sa_recima:
        if ime_fajla in lista_svih_fajlova:
            lista_AND_fajlova.append(ime_fajla)

    return lista_AND_fajlova

def OR_pretraga_za_vise_od_dva_kriterijuma(imena_fajlova, rec):
    OR_fajlovi = []
    for ime_fajla in objekat_cvora:
        vertex_trie = objekat_cvora[ime_fajla]._element[ime_fajla]
        ponavljanje_trazene_reci, _ = vertex_trie.search(rec.lower())
        if ponavljanje_trazene_reci != 0:
            OR_fajlovi.append(ime_fajla)

    for naziv_fajla in OR_fajlovi:
        if naziv_fajla not in imena_fajlova:
            imena_fajlova.append(naziv_fajla)

    return imena_fajlova

"""===================================================== AND, OR, NOT- PRETRAGA ==================================================="""
def da_li_ste_mislili(rec):
    predlozene_reci=[]
    rec_za_proveru=rec[:-1]
    for rec in pronadjene_reci:
        if rec.lower().startswith(rec_za_proveru.lower()):
            predlozene_reci.append(rec)

    if not predlozene_reci:
        da_li_ste_mislili(rec_za_proveru.lower())

    if len(rec_za_proveru.lower()) == 1:
        return predlozene_reci

    else:
        print("Hmmmm, da niste mozda ipak mislili na ove reci? :))")
        for i in range(len(predlozene_reci)):
            if i>11:
                break
            print("- "+predlozene_reci[i])
        return

def unesi_broj_stranica():
    while True:
        broj_stranica = input("Unesite broj stranica za prikaz: ")
        if not broj_stranica.isnumeric():
            print("Neispravan unos! Broj stranica ne moze biti nista drugo osim broja!")
            continue
        return broj_stranica

def AND_OR_NOT_pretrazivanje():
    while True:
        validnost_pretrage = True
        lista_operatera = ["NOT", "OR", "AND"]
        reci = input("Unesite reci za koje zelite da se vrsi pretraga po fajlovima: ")
        lista_reci = reci.split(" ")
        if (lista_reci[-1] in lista_operatera) or(lista_reci[0] in lista_operatera):
            print("Logicki operateri se ne mogu nalaziti na prvom ili poslednjem mestu!")
            continue
        else:
            for pozicija in range(len(lista_reci) - 1):
                pozicija1 = pozicija + 1
                if (lista_reci[pozicija] in lista_operatera) and (lista_reci[pozicija1] in lista_operatera):
                    print("Logicki operateri se ne mogu nalaziti jedan do drugog!")
                    validnost_pretrage = False
                    break
        if validnost_pretrage:
            break
    broj_stranica = unesi_broj_stranica()
    pronadji_reci_u_fajlovima(lista_reci, broj_stranica)

def pronadji_reci_u_fajlovima(lista_reci, broj_stranica):
    lista_operanada = ["AND", "OR", "NOT"]
    if (lista_operanada[0] not in lista_reci) and (lista_operanada[1] not in lista_reci) and (lista_operanada[2] not in lista_reci):
        #pomoc pri rang.-recnik ciji ce kljuc biti rec-unutar se nalazi 2. recnik-naziv fajla, gde se safrze informacije o [score reci, [susedne reci za prikaz], ...]
        #Naziv fajla predstavlja kljuc cvora, element Vertex-a je recnik, dok je vrednost oformljeni Trie za dati fajl
        pomoc_pri_rangiranju = {}
        for rec in lista_reci:
            svi_fajlovi = {}
        
            for kljuc_cvora in objekat_cvora:
                svi_fajlovi[kljuc_cvora] = []
            # pravimo recnik-kljuc: rec, sadrzi gde nam se za neku rec pojavljuju svi fajlovi u kojima se ona pojavljuje
            pomoc_pri_rangiranju[rec] = svi_fajlovi
        for rec in lista_reci:
            for kljuc in objekat_cvora:

                ukupan_broj_ponavljanja_reci_u_fajlovima = 0

                trie_vertex = objekat_cvora[kljuc]._element[kljuc]
                grane_vertex = graf.incident_edges(objekat_cvora[kljuc], False)

                broj_grana = 0
                grane = []
                # nalazimo trazenu rec i njen trie, gledamo njen broj ponavljanja unutar linka
                trazena_rec = rec.lower()
                broj_ponavljanja, susedne_reci = trie_vertex.search(trazena_rec)
                vertex_grana = {}

                for grana in grane_vertex:
                    broj_grana += 1
                    grane.append(grana)
                #dobijamo odredjenu vrednost spram povezanosti naseg linka sa drugim linkovima, prebrojavamo
                for grana in grane:
                    vertex_fajla = grana._origin
                    kljuc_vertex = list(vertex_fajla._element.keys())
                    vrednost = vertex_fajla._element[kljuc_vertex[0]]
                    vertex_grana[kljuc_vertex[0]] = vrednost
                #izvlacimo trie i broj ponavaljanja reci, interesuje nas ukupan broj ponavljanja nase reci
                for kljuc_vertexa in vertex_grana.keys():
                    fajl_trie = vertex_grana[kljuc_vertexa]
                    broj_ponavljanja_linkova_fajl, _ = fajl_trie.search(trazena_rec)
                    ukupan_broj_ponavljanja_reci_u_fajlovima += broj_ponavljanja_linkova_fajl
                
                rangiranje_reci = ukupan_broj_ponavljanja_reci_u_fajlovima + broj_grana + 30 * broj_ponavljanja

                if broj_ponavljanja == 0:
                    pomoc_pri_rangiranju[rec][kljuc].append(0)

                else:
                    pomoc_pri_rangiranju[rec][kljuc].append(rangiranje_reci)

                pomoc_pri_rangiranju[rec][kljuc].append(susedne_reci)

        rec_nije_pronadjena = True
        for rec in pomoc_pri_rangiranju:
            for ime_fajla in pomoc_pri_rangiranju[rec]:
                if pomoc_pri_rangiranju[rec][ime_fajla][0] > 90:
                    rec_nije_pronadjena = False
                    break
            if rec_nije_pronadjena:
                da_li_ste_mislili(rec)
                print("")
                print("Da li zelite da nastavite dalju pretragu u trenutnom repozitorijumu?")
                print("[1] Nastavi pretragu u trenutnom repozitorijumu")
                print("[2] Nastavi pretragu u novoodabranom repozitorijumu")
                print("[3] Zavrsi sa pretragom")
                print("[X]    UKOLIKO NISTA NE ODABERETE VRACATE SE NA POCETAK APLIKACIJE    [X]")
                print("---------------------------------------------------------------------------")
                odabir=input(">>> ")
                if odabir=="1":
                    AND_OR_NOT_pretrazivanje()
                elif odabir=="2":
                    subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
                elif odabir=="3":
                    quit()
                else:
                    subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
        rezultat_pretrage_bez_operatera(pomoc_pri_rangiranju, broj_stranica)
    else:
        reci_za_pretragu = [lista_reci[0], lista_reci[2]]

        if lista_reci[1] == lista_operanada[0]:
            rezultat = AND_pretraga_za_dva_kriterijuma(reci_za_pretragu)

        elif lista_reci[1] == lista_operanada[2]:
            rezultat = NOT_pretraga_za_dva_kriterijuma(reci_za_pretragu)

        elif lista_reci[1]==lista_operanada[1]:
            rezultat = OR_pretraga_za_dva_kriterijuma(reci_za_pretragu)

        if not rezultat:
            print("Ummmm, ne postoji rezultat koji zadovoljava Vase kriterijume! Vise srece drugi put :)")
            print("-------------------------------------------------------------------------------------------------")
            print("Da li zelite ponovo da pretrazite dati folder ili ipak zelite da pretrazite drugi direktorijum?")
            print("[1] Ponovo pretrazi dati folder")
            print("[2] Pretrazi drugi direktorijum")
            print("[3] Zavrsi pretragu")
            print("[X]   UKOLIKO NE ODABERETE NISTA- VRACATE SE NA PONOVNU PRETRAGU DIREKTORIJUMA   [X]")
            izbor=input(">>> ")
            if izbor=="1":
                AND_OR_NOT_pretrazivanje()
            elif izbor=="2":
                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
            elif izbor=="3":
                quit()
            else:
                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])

        else:
            # proveravamo da li je lista duza od 3, ako jeste-znamo da operator treba da se nalazi na svaka sledeca 2 mesta iza
            if len(lista_reci) >= 4:
                for pozicija in range(3, len(lista_reci), 2):
                    pozicija_reci=pozicija+1
                    rec = lista_reci[pozicija_reci]
                    operator = lista_reci[pozicija]
                    if operator == "NOT":
                        rezultat = NOT_pretraga_za_vise_od_dva_kriterijuma(rezultat, rec)
                        if not rezultat:
                            print(
                                "Ummmm, ne postoji fajl koji zadovoljava Vase kriterijume... Vise srece drugi put heh :)")
                            print(
                                "-------------------------------------------------------------------------------------------------")
                            print(
                                "Da li zelite ponovo da pretrazite dati folder ili ipak zelite da pretrazite drugi direktorijum?")
                            print("[1] Ponovo pretrazi dati folder")
                            print("[2] Pretrazi drugi direktorijum")
                            print("----- UKOLIKO NE ODABERETE NISTA- VRACATE SE NA PONOVNU PRETRAGU DIREKTORIJUMA ----")
                            izbor = input(">>> ")
                            if izbor == "1":
                                AND_OR_NOT_pretrazivanje()
                            elif izbor == "2":
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
                            else:
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])

                    elif operator == "AND":
                        rezultat = AND_pretraga_za_vise_od_dva_kriterijuma(rezultat, rec)
                        if not rezultat:
                            print(
                                "Ummmm, ne postoji fajl koji zadovoljava Vase kriterijume... Vise srece drugi put heh :)")
                            print(
                                "-------------------------------------------------------------------------------------------------")
                            print(
                                "Da li zelite ponovo da pretrazite dati folder ili ipak zelite da pretrazite drugi direktorijum?")
                            print("[1] Ponovo pretrazi dati folder")
                            print("[2] Pretrazi drugi direktorijum")
                            print("----- UKOLIKO NE ODABERETE NISTA- VRACATE SE NA PONOVNU PRETRAGU DIREKTORIJUMA ----")
                            izbor = input(">>> ")
                            if izbor == "1":
                                AND_OR_NOT_pretrazivanje()
                            elif izbor == "2":
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
                            else:
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])

                    elif operator == "OR":

                        rezultat = OR_pretraga_za_vise_od_dva_kriterijuma(rezultat, rec)
                        if not rezultat:
                            print(
                                "Ummmmm, ne postoji fajl koji zadovoljava Vase kriterijume... Vise srece drugi put heh :)")
                            print(
                                "-------------------------------------------------------------------------------------------------")
                            print(
                                "Da li zelite ponovo da pretrazite dati folder ili ipak zelite da pretrazite drugi direktorijum?")
                            print("[1] Ponovo pretrazi dati folder")
                            print("[2] Pretrazi drugi direktorijum")
                            print("----- UKOLIKO NE ODABERETE NISTA- VRACATE SE NA PONOVNU PRETRAGU DIREKTORIJUMA ----")
                            izbor = input(">>> ")
                            if izbor == "1":
                                AND_OR_NOT_pretrazivanje()
                            elif izbor == "2":
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
                            else:
                                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
        reci = []
        # lista u kojoj se sadrze samo reci bez operatera
        # rezultat-imena fajlova u kojima se nalaze nase reci
        for pozicija in range(0, len(lista_reci), 2):
            reci.append(lista_reci[pozicija])
        rezultat_pretrage_u_slucaju_kada_imamo_prisutne_operatere(reci, rezultat, broj_stranica)

#ujedno i prikaz pretrage nakon obrade pretrage sa operaterima
def rezultat_pretrage_bez_operatera(pomoc_pri_rangiranju, broj_stranica):
    # vrednost sveukupnog ranga-broj pronadjenih stranica
    dobijeni_fajlovi = []
    sveukupno_rangirani_fajlovi = {}
    #pomoc pri rang.-recnik ciji ce kljuc biti rec-unutar se nalazi 2. recnik-naziv fajla, gde se safrze informacije o [score reci, [susedne reci za prikaz], ...]

    for ime_fajla2 in pomoc_pri_rangiranju:
        for naziv_fajla in pomoc_pri_rangiranju[ime_fajla2]:
            sveukupno_rangirani_fajlovi[naziv_fajla] = 0
        break

    for ime_fajla1 in pomoc_pri_rangiranju:
        for naziv_fajla in pomoc_pri_rangiranju[ime_fajla1]:
            sveukupno_rangirani_fajlovi[naziv_fajla] += pomoc_pri_rangiranju[ime_fajla1][naziv_fajla][0]

    broj_pronadjenih_rezultata = list(sveukupno_rangirani_fajlovi.values())

    prikazi_rezultat = True
    rezultat_pretrage = 0
    while prikazi_rezultat:
        for broj_stranica_za_prikaz in range(int(broj_stranica)):

            if int(broj_stranica) > len(broj_pronadjenih_rezultata):
                print("Prikaz " + broj_stranica + " nije moguc!")
                return
            #uklanjamo index html kao top stranicu za prikaz svuda
            vodeca_stranica_za_prikaz = max(broj_pronadjenih_rezultata)
            broj_pronadjenih_rezultata.remove(vodeca_stranica_za_prikaz)

            for ime_fajla in sveukupno_rangirani_fajlovi:
                if sveukupno_rangirani_fajlovi[ime_fajla] == vodeca_stranica_za_prikaz and (ime_fajla not in dobijeni_fajlovi):
                    vodeci_fajl_za_prikaz = ime_fajla
                    dobijeni_fajlovi.append(ime_fajla)
                    break

            prikazivanje_fajla = 0
            for rec in pomoc_pri_rangiranju:
                for ime_fajla in pomoc_pri_rangiranju[rec]:
                    if vodeci_fajl_za_prikaz == ime_fajla:
                        prikazivanje_fajla += 1

                        prikazi_isecak_iz_fajla = ""

                        susedne_reci = pomoc_pri_rangiranju[rec][ime_fajla][1]

                        for susedna_rec in susedne_reci:

                            for pozicija in range(len(susedna_rec)):

                                if susedna_rec[pozicija].lower() == rec:
                                    susedna_rec[pozicija] = "(" + susedna_rec[pozicija].upper() + ")"

                                if pozicija == len(susedna_rec) - 1:
                                    prikazi_isecak_iz_fajla += susedna_rec[pozicija] + "\n"

                                else:
                                    prikazi_isecak_iz_fajla += susedna_rec[pozicija] + " "
                            prikazi_isecak_iz_fajla += "------------------------------------------------------------------------------------------------------------------\n"
                        if not prikazi_isecak_iz_fajla:
                            prikazi_isecak_iz_fajla += "Nazalost nismo uspeli da nadjemo rezultate spram vasih kriterijuma! Pokusajte ponovo :)"
                        print("")
                        print("Rec: " + rec)
                        print("Naziv fajla: " + str(vodeci_fajl_za_prikaz))
                        print("Isecak svih pojavljivanja date reci: \n" + prikazi_isecak_iz_fajla)
                        print("===========================================================================================================================================")

        while True:
            print("[1] Nastavite sa pretragom trenutnog direktorijuma")
            print("[2] Pretraga novog direktorijuma")
            print("[3] Zavrsi pretragu")
            print("[N] Prikazi jos isecaka ukoliko postoje  ")
            dalji_prikaz = input(">>> ")

            if dalji_prikaz=="1":
                AND_OR_NOT_pretrazivanje()
            elif dalji_prikaz=="2":
                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
            elif dalji_prikaz == "N":
                break
            elif dalji_prikaz == "3":
                quit()           
            else:
                print("GRESKA! Niste odabrali nijednu od ponudjenih opcija- vracate se na start aplikacije")
                pokreni_pretrazivac()

#pomoc za rangiranje recnik{trazena rec{stranica na kojoj se pojavjluje[]}}
def rezultat_pretrage_u_slucaju_kada_imamo_prisutne_operatere(lista_reci, imena_fajlova, broj_stranica):

    pomoc_za_rangiranje = {}
    for rec in lista_reci:
        svi_fajlovi = {}
        for kljuc in objekat_cvora:
            for ime_fajla in imena_fajlova:
                if kljuc == ime_fajla:
                    svi_fajlovi[kljuc] = []
        pomoc_za_rangiranje[rec] = svi_fajlovi

    for rec in lista_reci:
        for kljuc1 in objekat_cvora:
            if kljuc1 in pomoc_za_rangiranje[rec]:
                broj_grana = 0
                grane = []

                grane_vertex = graf.incident_edges(objekat_cvora[kljuc1], False)
                trie_vertex = objekat_cvora[kljuc1]._element[kljuc1]
                broj_ponavljanja, susedne_reci = trie_vertex.search(rec.lower())

                for grana in grane_vertex:
                    broj_grana += 1
                    grane.append(grana)

                grana_vertex = {}

                for grana in grane:
                    vertex_fajl = grana._origin
                    kljuc = list(vertex_fajl._element.keys())
                    vrednost_grane_vertexa = vertex_fajl._element[kljuc[0]]
                    grana_vertex[kljuc[0]] = vrednost_grane_vertexa

                broj_ponavljanja_svih_linkova = 0
                for kljuc2 in grana_vertex:
                    trie_za_fajl = grana_vertex[kljuc2]
                    broj_ponavljanja_linka, _ = trie_za_fajl.search(rec.lower())
                    broj_ponavljanja_svih_linkova += broj_ponavljanja_linka

                rangirani_fajl = broj_grana + 30*broj_ponavljanja + broj_ponavljanja_svih_linkova

                if broj_ponavljanja == 0:
                    pomoc_za_rangiranje[rec][kljuc1].append(0)
                else:
                    pomoc_za_rangiranje[rec][kljuc1].append(rangirani_fajl)
                pomoc_za_rangiranje[rec][kljuc1].append(susedne_reci)

    rec_nije_pronadjena_u_fajlu = True
    for rec in pomoc_za_rangiranje:
        for ime_fajla in pomoc_za_rangiranje[rec]:
            if pomoc_za_rangiranje[rec][ime_fajla][0] > 150:
                rec_nije_pronadjena_u_fajlu = False
                break

        if rec_nije_pronadjena_u_fajlu:
            da_li_ste_mislili(rec)
            print("")
            print("Da li zelite da nastavite dalju pretragu u trenutnom repozitorijumu?")
            print("[1] Nastavi pretragu u trenutnom repozitorijumu")
            print("[2] Nastavi pretragu u novoodabranom repozitorijumu")
            print("[3] Zavrsi pretragu")
            print("[X]    UKOLIKO NISTA NE ODABERETE VRACATE SE NA POCETAK APLIKACIJE    [X]")
            print("---------------------------------------------------------------------------")
            odabir = input(">>> ")

            if odabir == "1":
                AND_OR_NOT_pretrazivanje()

            elif odabir == "2":
                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])
                
            elif odabir == "3":
                quit()  
            else:
                subprocess.call([sys.executable, os.path.realpath(__file__)] +sys.argv[1:])

    rezultat_pretrage_bez_operatera(pomoc_za_rangiranje, broj_stranica)

"""===================================================== POKRENI APLIKACIJU ======================================================"""

def pokreni_pretrazivac():
    # napravi funkciju gde korisinik bira putanju u kojoj zeli da se iscitaju svi html fajlovi
    # nalazi html fajlove, ucitava ih, konstruisemo graph i trie
    # ucitava fajlove iz korenskog direktorijuma
    print("------------------------- TEKSTUALNI SEARCH ENGINE -------------------------")
    print("")
    print("                             >>> KORAK 1 <<<                                ")
    print("Unesite putanju (bez navodnika) unutar koje se vrsi pretraga: ")

    naziv_foldera = input(">>> ")
    print("")
    if os.path.exists(naziv_foldera) or os.path.isdir(naziv_foldera):
        print("Molimo za momenat strpljenja... Podaci se ucitavaju :)")
        ucitaj_fajlove(naziv_foldera)
        ubaci_podatke_u_grane()
        print("Broj cvorova je : ", graf.vertex_count())
        print("Broj ivica je : ", graf.edge_count())
        odabir_korisnika()
    else:
        print("Uneli ste nepostojeci naziv direktorijuma! Molimo Vas pokusajte ponovo sa posotojecim direktorijumom!")
        print("")
        pokreni_pretrazivac()

    # stavlja podatke u edges
pokreni_pretrazivac()