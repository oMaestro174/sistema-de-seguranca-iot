#include <ArduinoUnit.h>
#include <math.h>

// Função para verificar a senha
bool checkPassword(String password) {
  return password == "1234";
}

// Função para detectar movimento com base em aceleração e giroscópio
bool checkMotion(float ax, float ay, float az, float gx, float gy, float gz) {
  float gyro = sqrt(gx * gx + gy * gy + gz * gz);
  if (gyro > 0.5) return true;

  float accel = sqrt(ax * ax + ay * ay + az * az);
  return fabs(accel - 1.0) > 0.1;
}

// 🧪 Testes com ArduinoUnit

test(senha_correta) {
  assertTrue(checkPassword("1234"));
}

test(senha_errada) {
  assertFalse(checkPassword("9999"));
}

test(movimento_gyro) {
  assertTrue(checkMotion(0, 0, 1, 0.6, 0, 0));
}

test(movimento_accel) {
  assertTrue(checkMotion(0, 0, 0.7, 0, 0, 0));
}

test(sem_movimento) {
  assertFalse(checkMotion(0, 0, 1, 0, 0, 0));
}


void setup() {
  Serial.begin(9600);
}

void loop() {
  Test::run();  // Executa os testes
}
