def _parse_lines(self):
    # Zastavica koja oznacava nalazimo li se trenutno u viselinijskom komentaru.
    self._comment = False
    
    # Za svaku liniju u izvornoj datoteci pozivamo funkciju _parse_comments.
    self._iter_lines(self._parse_line)

# Funkcija prima originalnu liniju iz asemblerske datoteke, trenutni broj linije
# u kojoj se nalazimo i originalan broj linije iz asemblerske datoteke.
#
# Vraca liniju bez razmaka i komentara. Ukoliko je cijela linija prazna ili
# unutar komentara, vracamo prazan string. Viselinijske komentare parsiramo
# koristeci zastavicu "_comment".
#
# Jednolinijski komentar zapocinjemo s "//", dok se viselinijski komentar nalazi
# unutar znakova "/*" i "*/".
def _parse_line(self, line, p, o):
    l = ""
    i = 0
    if line[0] == "@":
        a = line.split()
        a.pop(0)
        if len(a) != 0:
            self._flag = False
            self._line = o
            self._errm = "Invalid operation | " + "".join(a) + "."
            return ""
    
    if line[0] == "(":
        b = line.split(")")
        b.pop(0)
        if len(b) != 0 and b[0] != "\n":
            self._flag = False
            self._line = o
            self._errm = "Invalid operation | " + "".join(b) + "."
            return ""

    while i < len(line) - 1:
        p = line[i] + line[i + 1]

        if (self._comment == False and p == "/*") or (self._comment and p == "*/"):
            self._comment = not self._comment
            i += 1
        elif self._comment == False and p == "*/":
            self._flag = False
            self._line = o
            self._errm = "Unbalanced comment delimiter"
        elif (p == "//"):
            break
        elif line[i].isspace() == False and self._comment == False:
            l += line[i]

        i += 1
    return l
