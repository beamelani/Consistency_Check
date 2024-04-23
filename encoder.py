#variables è un elenco di tutte le variabili della formula e time variable sono le variabili con una istanza
#con un valore per ogni istante di tempo, dove gli istanti di tempo sono calcolati come uno
#per ogni istante del time horizon della formula. Expression invece è il risultato del visiting
# ovvero un dict in cui ogni elemento è una proposizione espressa come una lista e che parte dalle
#prop atomiche e man mano le compone (albero)

#stl_expression = "G[0,5] ((x > 3) && (F[2,7] (y < 2)))"
#propositions = [['x', '>', '3'], ['y', '<', '2'], ['F', '2', '7', '_phi1'], ['&&', '_phi0', '_phi2'], ['G', '0', '5', '_phi3']]
#variables = ['x', 'y']
#formula_horizon = 13
#time variable=  {'x0': None, 'x1': None, 'x2': None, 'x3': None, 'x4': None, 'x5': None, 'x6': None, 'x7': None, 'x8': None, 'x9': None, 'x10': None, 'x11': None, 'x12': None, 'y0': None, 'y1': None, 'y2': None, 'y3': None, 'y4': None, 'y5': None, 'y6': None, 'y7': None, 'y8': None, 'y9': None, 'y10': None, 'y11': None, 'y12': None}
class Encoder:
    def visit_expression(self, formula_horizon, variables, time_variables, propositions):
        for variable in variables: #for each variable in the formula
            next_prop = variable
            for phi in propositions: #check the propositions to reconstruct the constraints for the variable at every time instant
                if next_prop in phi and (len(phi)==1 or phi[1] in {'<', '>', '<=', '>=', '==', '>'}): #cerca l'espressione atomica (bool o reale) in cui compare la variabile
                    constraint = phi
                    next_prop = f"_phi{propositions.index(phi)}" #aggiorno next_prop per seguire i vincoli sulla variabile x
                elif next_prop in phi and phi[0] in {'&&', '||'}:
                    next_prop = f"_phi{propositions.index(phi)}"
                    return self.logical_relationship(variable, constraint, phi)
                elif next_prop in phi and phi[0] in {'G'}:
                    next_prop = f"_phi{propositions.index(phi)}"
                    #devi trovare un modo per verificare se l'operatore temporale è annidato o meno, per calcolare che
                    #istanti di tempo interessa nell'orizzonte temporale della formula e passare l'info alla funzione sotto
                    return self.globally()
                elif next_prop in phi and phi[0] in {'F'}:
                    next_prop = f"_phi{propositions.index(phi)}"
                    return self.eventually()





    #Encoding di Globally: deve mettere in and le espressioni (start e end però potrebbero non corrispondere a quelli
    #del globally se è nested
    def globally(self, phi, start, end, propositions):
        if phi in propositions[-1]: #se G è in il primo operatore temporale

        return

    #Encoding di Eventually
    def eventually(self, phi, start, end):
        return

    #Encoding logical relationship
    def logical_relationship(self, variable, constraint, phi):
        return


#Esempio
#stl_expression = "G[0,5] (x > 3)"
propositions=  [['x', '>', '3'], ['G', '0', '5', '_phi0']]
formula_horizon = 6
variables= ['x']
time_variables = {'x0': None, 'x1': None, 'x2': None, 'x3': None, 'x4': None, 'x5': None}
encoder = Encoder()
result = encoder.visit_expression(formula_horizon, variables, time_variables, propositions)