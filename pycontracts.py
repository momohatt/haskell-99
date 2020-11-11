from contracts import contract, new_contract

@contract
def add(a: int, b: int):
    return a+b

add(1, 2)
add(-1, 2)
# add([1], [2]) # Error

@contract
def pos_add(a: 'int,>0', b: int):
    return a+b

pos_add(1, 2)
# pos_add(-1, 2) # Error

@contract(a=int, l='list[N]', returns='list[N+1]')
def prepend(a, l):
    l.insert(0, a)
    return l

l = prepend(3, [2, 1, 4])

@contract
def myabs(x: int) -> 'int,>0':
    return abs(x)

myabs(-1)
myabs(1)

new_contract('valid_name', lambda s: isinstance(s, str) and len(s)>0)
@contract(names='dict(int: (valid_name, int))')
def process_accounting(names):
    ...
