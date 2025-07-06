// checkMotion.c
#include <stdbool.h>
#include <math.h> // Para abs e sqrt se usar magnitude

// Limites para detecção de movimento (ajuste para o CBMC)
// Esses valores devem ser compatíveis com os que você usará no Arduino.
#define ACCEL_THRESHOLD_CBMC 0.1 // Exemplo: um pequeno limiar
#define GYRO_THRESHOLD_CBMC 0.1 // Exemplo: um pequeno limiar em graus/s

// Função a ser verificada
bool checkMotion(float accelX, float accelY, float accelZ, float gyroX, float gyroY, float gyroZ) {
    // A lógica deve ser a mesma da sua implementação no Arduino para a parte de decisão.
    // Para CBMC, simplifique para focar na propriedade.
    // Se a magnitude do vetor de aceleração menos 1g for grande, ou se qualquer giro for grande, então há movimento.

    // Aceleração: verifica se o desvio da aceleração em relação ao estado de repouso (1g em um eixo, 0 nos outros) é grande.
    // Para simplificar, vamos verificar se qualquer componente de aceleração (além da gravidade em um eixo) é significativa.
    // Ou a magnitude do giroscópio.
    
    // Se a MPU está parada e alinhada com um eixo da gravidade, teríamos algo como (0,0,1)g.
    // A propriedade é que *se o movimento é abaixo do limite*, deve retornar false.
    // E *se o movimento está acima do limite*, deve retornar true.

    float currentGyroMagnitude = sqrt(gyroX*gyroX + gyroY*gyroY + gyroZ*gyroZ);

    if (currentGyroMagnitude > GYRO_THRESHOLD_CBMC) {
        return true; // Movimento de rotação detectado
    }

    // Para aceleração, é um pouco mais complexo, pois 1g é sempre presente.
    // Se a MPU está parada, a magnitude do vetor aceleração total é aproximadamente 1.0.
    // Movimento linear causará desvios nesse valor ou grandes variações.
    float accelMagnitude = sqrt(accelX*accelX + accelY*accelY + accelZ*accelZ);
    if (fabs(accelMagnitude - 1.0) > ACCEL_THRESHOLD_CBMC) { // Se a magnitude total varia muito de 1g
        return true; // Movimento de deslocamento detectado
    }
    
    return false; // Movimento mínimo
}

// Função principal para o CBMC
int main() {
    float gx, gy, gz; // Valores para o giroscópio
    float ax, ay, az; // Valores para o acelerômetro

    // Fazer as variáveis não determinísticas
    __CPROVER_havoc_float(gx);
    __CPROVER_havoc_float(gy);
    __CPROVER_havoc_float(gz);
    __CPROVER_havoc_float(ax);
    __CPROVER_havoc_float(ay);
    __CPROVER_havoc_float(az);

    // Propriedade 1: Se o movimento está abaixo do limite, checkMotion deve retornar false.
    // Assumimos que os valores de giro e a variação da aceleração são menores que os limites.
    __CPROVER_assume(sqrt(gx*gx + gy*gy + gz*gz) <= GYRO_THRESHOLD_CBMC);
    __CPROVER_assume(fabs(sqrt(ax*ax + ay*ay + az*az) - 1.0) <= ACCEL_THRESHOLD_CBMC);
    __CPROVER_assert(checkMotion(ax, ay, az, gx, gy, gz) == false, "checkMotion deve retornar false se movimento abaixo do limite");

    // Reinicialize variáveis para a próxima asserção se necessário ou faça um novo `main` para cada propriedade
    // Propriedade 2: Se o movimento está acima do limite, checkMotion deve retornar true.
    // Assumimos que PELO MENOS um dos componentes excede o limite.
    __CPROVER_assume(sqrt(gx*gx + gy*gy + gz*gz) > GYRO_THRESHOLD_CBMC || 
                     fabs(sqrt(ax*ax + ay*ay + az*az) - 1.0) > ACCEL_THRESHOLD_CBMC);
    __CPROVER_assert(checkMotion(ax, ay, az, gx, gy, gz) == true, "checkMotion deve retornar true se movimento acima do limite");

    return 0;
}