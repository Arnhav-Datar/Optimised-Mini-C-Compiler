%{  
    // #if defined(__cplusplus) 
    // extern "C" {
    // #endif
    #include "y.tab.hpp"
    int print();
    extern char mytext[10000];
    // #if defined(__cplusplus)
    // }
    // #endif
    extern int lno; 
    extern int lnif; 
%}

digit [0-9]
hexdigit [0-9a-f]
letter [a-zA-Z]
hex "0x"
Ls "l"|"ll"|"L"|"LL"|"u"|"U"
percentD \"%d\\n\"
number {digit}+(\.{digit}+)?(e[+-]?{digit}+)?{Ls}?  
integer {digit}+{Ls}?
hexinteger {hex}{hexdigit}+{Ls}?
identifier ({letter}|_)({letter}|_|{digit})*
delim [ \t]
all ({delim}|.)
whiteSpace {delim}+
colon :
semicolon ;
dot \.
comma ,

%%

"//".*[\n] {
   lno++;
}

"/*"([^*]|\*+[^*/])*\*+"/" {
    for(int i=0; i<strlen(yytext); i++)
        if(yytext[i]=='\n')
            lno++;
}

\n {
    lno++;
}

"/*" {
    printf("***lexing terminated*** [lexer error]: ill-formed comment\n");
    exit(0);
}

{percentD} {
    return PERCENTD;
}
\"%d\" {
    return PERD;
}

\"([^\n"\\]|\\.)*\" {
    return STRLITERAL;
}

'(\\.|[^\n\\'])+' {
    return CHARLITERAL;
}

int {
    return INT;
}

float {
    return FLOAT;
}

char {
    return CHAR;
}

long {
    return LONG;
}

double {
    return DOUBLE;
}

short {
    return SHORT;
}

void {
    return VOID;
}

if {
    lnif=lno;
    return IF;
}

else {
    return ELSE;
}

for {
    return FOR;
}

while {
    return WHILE;
}

do {
    return DO;
}

switch {
    return SWITCH;
}

case {
    return CASE;
}

struct {
    return STRUCT;
}

break {
    return BREAK;
}

continue {
    return CONTINUE;
}

return {
    return RETURN;
}

sizeof {
    return SIZEOF;
}

default {
    return DEFAULT;
}

extern {
    return EXTERN;
}

printf {
    return PRINTF;
}
scanf {
    return SCANF;
}

{integer} {
    strcpy(mytext, yytext);
    return INTEGER_NUMBER;
}

{hexinteger} {
    strcpy(mytext, yytext);
    return INTEGER_NUMBER;
}

{number} {
    strcpy(mytext, yytext);
    return FLOAT_NUMBER;
}

{identifier} {
    print();
    strcpy(mytext, yytext);
    return IDENTIFIER;
}

"->"|"++"|"--" {
    if(strcmp(yytext, "++") == 0) {
        return INC;
    }
    else if(strcmp(yytext, "--") == 0) {
        return DEC;
    }
    else if(strcmp(yytext, "->") == 0) {
        return ARROW;
    }
}

[&|^~] {
    char ch = yytext[0];
    switch (ch) {
        case '&' : return BITAND;
            break;
        case '|' : return BITOR;
             break;
        case '^' : return BITXOR;
            break;
        case '~' : return BITNOT;
            break;
    }
}

"&&"|"||"|"!" {
    if(strcmp(yytext, "&&") == 0) {
        return AND;
    }
    else if(strcmp(yytext, "||") == 0) {
        return OR;
    }
    else if(strcmp(yytext, "!") == 0) {
        return NOT;
    }
}

[%*+/-] {
    char ch = yytext[0];
    switch (ch) {
        case '+' : return PLUS;
            break;
        case '-' : return MINUS;
             break;
        case '*' : return MULT;
            break;
        case '/' : return DIV;
            break;
        case '%' : return MOD;
            break;
    }
}

"=="|"<="|">="|">"|"<"|"<=>"|"!=" {
    if(strcmp(yytext, "==") == 0) {
        return EQEQ;
    }
    else if(strcmp(yytext, ">=") == 0) {
        return GEQ;
    }
    else if(strcmp(yytext, "<=") == 0) {
        return LEQ;
    }
    else if(strcmp(yytext, ">") == 0) {
        return GT;
    }
    else if(strcmp(yytext, "<") == 0) {
        return LT;
    }
    else if(strcmp(yytext, "!=") == 0) {
        return NEQ;
    }
    else if(strcmp(yytext, "<=>") == 0){
        return NEWOP;
    }   
}

\= {
    return EQ;
}

"(" {
    return '(';
}

")" {
    return ')';
}

"[" {
    return '[';
}

"]"  {
    return ']';
}

"{" {
    return '{';
}

"}" {
    return '}';
}

{whiteSpace} {
   
}

{dot} {
    return '.'; 
}

{colon} {
    return ':';
}

{comma} {
    print();
    return ',';
}

{semicolon} {
    return ';';
}

. {
    
}

%%

int print() {
    // printf("%s\n", yytext);
    return 0;
}

int yywrap(void) {
    return 1;
}
