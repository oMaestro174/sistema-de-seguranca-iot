// checkPassword.c
#include <string.h>
#include <stdbool.h>

// Definir a senha correta para o CBMC
#define CORRECT_PASSWORD "1234"
#define PASSWORD_LENGTH 4

// Função a ser verificada
bool checkPassword(const char* password) {
    if (strlen(password) != PASSWORD_LENGTH) {
        return false;
    }
    return strcmp(password, CORRECT_PASSWORD) == 0;
}

// Função principal para o CBMC (entry point)
int main() {
    char password[PASSWORD_LENGTH + 1]; // +1 para o null terminator
    
    // Fazer a variável password não determinística para o CBMC explorar todos os casos
    __CPROVER_havoc_memory(password, sizeof(password));
    __CPROVER_assume(strlen(password) == PASSWORD_LENGTH); // Assumir que a senha tem o tamanho correto

    // Propriedade 1: Se a senha é "1234", checkPassword deve retornar true
    if (strcmp(password, CORRECT_PASSWORD) == 0) {
        __CPROVER_assert(checkPassword(password) == true, "checkPassword deve retornar true para a senha correta");
    } else {
    // Propriedade 2: Se a senha não é "1234", checkPassword deve retornar false
        __CPROVER_assert(checkPassword(password) == false, "checkPassword deve retornar false para senha incorreta");
    }

    return 0;
}