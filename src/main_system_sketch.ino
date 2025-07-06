// Inclui as bibliotecas necessárias para o projeto
#include <Keypad.h>    // Para o teclado matricial
#include <Wire.h>      // Para comunicação I2C com o MPU6050
#include <MPU6050_light.h> // Biblioteca MPU6050_light para o sensor de movimento
#include <Servo.h>     // Para o controle do servo motor
#include <math.h>      // Para funções matemáticas como fabs() e sqrt()


// Função não-determinística para CBMC
extern int nondet_init();

// --- Definições de Hardware ---
// Definições para o teclado matricial 4x4
const byte ROWS = 4; // Número de linhas
const byte COLS = 4; // Número de colunas
char keys[ROWS][COLS] = { // Mapeamento das teclas
  {'1','2','3','A'},
  {'4','5','6','B'},
  {'7','8','9','C'},
  {'*','0','#','D'}
};
byte rowPins[ROWS] = {9, 8, 7, 6}; // Pinos do Arduino conectados às linhas do teclado
byte colPins[COLS] = {5, 4, 3, 2}; // Pinos do Arduino conectados às colunas do teclado

// Cria o objeto Keypad
Keypad keypad = Keypad( makeKeymap(keys), rowPins, colPins, ROWS, COLS );

// Pino para o servo motor
const int SERVO_PIN = 10;
Servo myServo; // Cria o objeto Servo

// --- Variáveis de Estado do Sistema ---
// Enumeração para os estados da Máquina de Estados Finitos (FSM)
// Renomeado IDLE para SYSTEM_IDLE para evitar conflito com a biblioteca Keypad
enum SystemState {
  SYSTEM_IDLE,  // Estado inicial: aguardando o início da autenticação
  AUTH,         // Estado de autenticação: coletando a senha
  VERIFY,       // Estado de verificação: validando a senha
  MOTION_CHECK, // Estado de verificação de movimento: lendo o MPU6050
  UNLOCK        // Estado de desbloqueio: servo motor liberado
};

SystemState currentState = SYSTEM_IDLE; // Variável para armazenar o estado atual do sistema

// --- Variáveis de Lógica do Sistema ---
String passwordAttempt = ""; // Armazena a senha digitada pelo usuário
const String CORRECT_PASSWORD = "1234"; // Senha correta para acesso

unsigned long stateStartTime = 0; // Armazena o tempo em que o estado atual foi iniciado
const unsigned long MOTION_CHECK_DURATION = 2000; // Duração do estado MotionCheck em ms (2 segundos)
const unsigned long UNLOCK_DURATION = 5000;       // Duração do estado Unlock em ms (5 segundos)

// Objeto MPU6050 - Passa o objeto Wire para comunicação I2C
MPU6050 mpu(Wire); 

// Limiares para detecção de movimento (ajuste conforme necessário após testes)
// Estes valores são sensíveis e devem ser calibrados no ambiente real.
// Para giroscópio, valores próximos de 0 indicam pouco movimento angular.
// Para acelerômetro, a magnitude total deve ser próxima de 1g (9.8 m/s^2) quando parado.
const float GYRO_THRESHOLD = 0.5; // Limiar para detecção de rotação (graus/s)
const float ACCEL_VARIATION_THRESHOLD = 0.1; // Limiar para variação de aceleração (g)

// --- Funções Auxiliares (declaradas antes para que as funções de estado possam chamá-las) ---
bool checkPassword(String password);
bool checkMotion(float accelX, float accelY, float accelZ, float gyroX, float gyroY, float gyroZ);

// --- Funções de Manipulação de Estados (declaradas antes do setup/loop) ---
void handleIdleState();
void handleAuthState();
void handleVerifyState();
void handleMotionCheckState();
void handleUnlockState();

// --- Funções de Inicialização e Loop ---

void setup() {
  Serial.begin(9600); // Inicializa a comunicação serial para debug
  Wire.begin();       // Inicializa a comunicação I2C para o MPU6050

  // Inicializa o MPU6050
  // O método begin() da MPU6050_light não aceita parâmetros de escala/range.
  // Ele retorna um byte de status.
  byte status = mpu.begin();
  while(status != 0){ // Loop enquanto o sensor não é encontrado
    Serial.print("Erro ao inicializar MPU6050 (status: ");
    Serial.print(status);
    Serial.println("). Tentando novamente...");
    delay(1000);
    status = mpu.begin();
  }
  Serial.println("MPU6050 inicializado com sucesso!");

  // Calibra o MPU6050. Isso é importante para remover o offset.
  // MPU6050_light usa calcOffsets() para calibração de giroscópio e acelerômetro.
  Serial.println("Calibrando MPU6050... Mantenha o sensor parado.");
  delay(1000);
  mpu.calcOffsets(true,true); // Calibra acelerômetro e giroscópio
  Serial.println("Calibracao do MPU6050 concluida.");

  myServo.attach(SERVO_PIN); // Anexa o servo motor ao pino
  myServo.write(0); // Garante que o servo esteja na posição "bloqueado" (0 graus)

  Serial.println("Sistema de Seguranca Inicializado. Pressione '*' para comecar.");
}

void loop() {
  // O switch-case gerencia as transições entre os estados da FSM
  switch (currentState) {
    case SYSTEM_IDLE: // Usar SYSTEM_IDLE
      handleIdleState();
      break;
    case AUTH:
      handleAuthState();
      break;
    case VERIFY:
      handleVerifyState();
      break;
    case MOTION_CHECK:
      handleMotionCheckState();
      break;
    case UNLOCK:
      handleUnlockState();
      break;
  }
}

// --- Funções de Manipulação de Estados ---

// Estado IDLE: Aguarda o pressionamento da tecla '*' para iniciar a autenticação
void handleIdleState() {
  char key = keypad.getKey(); // Lê a tecla pressionada
  if (key == '*') {
    Serial.println("Entre com a senha de 4 digitos:");
    passwordAttempt = ""; // Limpa qualquer senha anterior
    currentState = AUTH;  // Transita para o estado AUTH
  }
}

// Estado AUTH: Coleta os 4 dígitos da senha
void handleAuthState() {
  char key = keypad.getKey(); // Lê a tecla pressionada
  if (key != NO_KEY) { // Se alguma tecla foi pressionada
    if (key >= '0' && key <= '9') { // Se for um dígito numérico
      passwordAttempt += key; // Adiciona o dígito à senha
      Serial.print("*");      // Exibe um asterisco para ocultar a senha no serial
      if (passwordAttempt.length() == 4) { // Se a senha tem 4 dígitos
        currentState = VERIFY; // Transita para o estado VERIFY
      }
    } else { // Se não for um dígito numérico
      Serial.println("\nCaractere invalido. Tente novamente.");
      passwordAttempt = ""; // Limpa a senha
      currentState = SYSTEM_IDLE;  // Retorna ao estado SYSTEM_IDLE
    }
  }
}

// Estado VERIFY: Verifica se a senha digitada é a correta
void handleVerifyState() {
  if (checkPassword(passwordAttempt)) { // Chama a função para verificar a senha
    Serial.println("\nSenha correta. Verificando movimento...");
    stateStartTime = millis(); // Registra o tempo de início para o estado MOTION_CHECK
    currentState = MOTION_CHECK; // Transita para o estado MOTION_CHECK
  } else {
    Serial.println("\nSenha incorreta. Acesso negado.");
    currentState = SYSTEM_IDLE; // Retorna ao estado SYSTEM_IDLE
  }
}

// Estado MOTION_CHECK: Lê o MPU6050 por um tempo para verificar movimento
void handleMotionCheckState() {
  // Verifica se o tempo de verificação de movimento ainda não se esgotou
  if (millis() - stateStartTime < MOTION_CHECK_DURATION) {
    mpu.update(); // Atualiza as leituras do MPU6050 (método correto para MPU6050_light)

    // Obtém os valores de aceleração e giroscópio
    // Usar fabsf() para valores float
    float accelX = mpu.getAccX();
    float accelY = mpu.getAccY();
    float accelZ = mpu.getAccZ();
    float gyroX = mpu.getGyroX();
    float gyroY = mpu.getGyroY();
    float gyroZ = mpu.getGyroZ();

    // Chama a função auxiliar para verificar se há movimento significativo
    if (checkMotion(accelX, accelY, accelZ, gyroX, gyroY, gyroZ)) {
      Serial.println("Movimento detectado durante a verificacao. Acesso negado.");
      currentState = SYSTEM_IDLE; // Retorna ao estado SYSTEM_IDLE se movimento for detectado
      return; // Sai da função para evitar processar o tempo restante
    }
  } else { // Se o tempo de verificação de movimento se esgotou (2 segundos)
    Serial.println("Movimento minimo. Acesso liberado.");
    stateStartTime = millis(); // Registra o tempo de início para o estado UNLOCK
    currentState = UNLOCK; // Transita para o estado UNLOCK
  }
}

// Estado UNLOCK: Ativa o servo motor para liberar o acesso e aguarda um tempo
void handleUnlockState() {
  myServo.write(90); // Move o servo para a posição "aberto" (ajuste o ângulo conforme seu servo)
  Serial.println("Porta aberta. Aguardando 5 segundos...");
  
  // Verifica se o tempo de desbloqueio se esgotou
  if (millis() - stateStartTime >= UNLOCK_DURATION) {
    myServo.write(0); // Move o servo de volta para a posição "fechado" (0 graus)
    Serial.println("Porta fechada. Sistema retornou ao Idle.");
    currentState = SYSTEM_IDLE; // Retorna ao estado SYSTEM_IDLE
  }
}

// --- Funções Auxiliares (para Testes de Unidade e CBMC) ---

// Função para verificar a senha
bool checkPassword(String password) {
  return password == CORRECT_PASSWORD;
}

// Função para verificar o movimento com base nas leituras do MPU6050
// Retorna true se houver movimento significativo, false caso contrário.
bool checkMotion(float accelX, float accelY, float accelZ, float gyroX, float gyroY, float gyroZ) {
  // Verifica se a magnitude do giroscópio (velocidade angular) excede o limiar
  // Um valor alto indica rotação
  float gyroMagnitude = sqrt(gyroX*gyroX + gyroY*gyroY + gyroZ*gyroZ);
  if (gyroMagnitude > GYRO_THRESHOLD) {
      return true; // Movimento de rotação detectado
  }

  // Verifica a variação da magnitude da aceleração em relação a 1g (gravidade)
  // Quando parado, a magnitude total da aceleração deve ser ~1g.
  // Variações significativas indicam movimento linear.
  float accelMagnitude = sqrt(accelX*accelX + accelY*accelY + accelZ*accelZ);
  // Usamos fabs (absolute float) para a diferença
  if (fabs(accelMagnitude - 1.0) > ACCEL_VARIATION_THRESHOLD) {
      return true; // Movimento de deslocamento detectado
  }
  
  return false; // Movimento mínimo (considerado parado)
}
