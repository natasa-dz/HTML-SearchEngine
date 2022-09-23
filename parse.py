# -*- coding: utf-8 -*-
import re
import os
from html.parser import HTMLParser
from typing import Tuple
from collections import OrderedDict
#from html.parser import ParsingError
#izmeni trie, nazive, komentare, sve
"-------------------------------------        TRIE  AND TRIENODE        --------------------------------------------"
class TrieNode:
    def __init__(self, value):
        self.value = value
        self.children = {}
        self.end_here = False
        self.file_path = None
        self.surroundings = []
        self.repeats = 0


class Trie:
    def __init__(self):
        self.root = TrieNode(None)

    def insert(self, word, file_path, surroundings):
        # ubaci rec u trie, argument: word, povratna_vrednost: void
        parent = self.root
        for i, char in enumerate(word):
            if char not in parent.children:
                parent.children[char] = TrieNode(char)
            parent = parent.children[char]
            if i == len(word) - 1:
                parent.end_here = True
                # ovako nesto da se zna u kojem je fajlu?
                parent.file_path = file_path
                # ovako nesto da se zna sta je oko te reci
                parent.surroundings.append(surroundings)
                parent.repeats += 1

    def search(self, word):
        # pronadji rec u trie, argument: word
        parent = self.root
        for char in word:
            if char not in parent.children:
                return 0, []
            parent = parent.children[char]
        return parent.repeats, parent.surroundings

    def starts_with(self, prefix):
        # autocomplete
        parent = self.root
        for char in prefix:
            if char not in parent.children:
                return False
            parent = parent.children[char]
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

parser=Parser()
podaci=parser.parse("C:\prj2_test\python-2.7.7-docs-html\genindex.html")

("---------------------------------------------------Meni--------------------------------------------------------------")
SEPARATOR=os.path.sep
graf=Graph(directed=True)
BASE_DIR=os.path.dirname(os.path.realpath(__file__))
pronadjene_reci=[]

def isprintaj_meni():
    print("1. Pretrazivanje pomocu unosa reci i logickih operatera"
          "2. Pretraga pomocu upotrebe fraza"
          "3. 'Da li ste mislili?' tip pretrage"
          "4. Izlazak")

def zavrseno_popunjavanje(lista_pronadjenih_reci):
    for rec in lista_pronadjenih_reci:
        if rec.lower() not in pronadjene_reci :
            pronadjene_reci.append(rec.lower())
print(SEPARATOR)

def ucitaj_fajlove(path):

    for file in os.listdir(path):
        if file.endswith("html"):
            putanja_fajla=path+SEPARATOR+file
            lista_pronadjenih_reci, fajl_linkovi=parser.parse(putanja_fajla)

            if not lista_pronadjenih_reci:
                continue
            zavrseno_popunjavanje(lista_pronadjenih_reci)


        if file.startswith("."):
            continue