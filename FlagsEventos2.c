//*****************************************************************************
//
// Codigo de la pr�ctica 2 de la asignatura de microb�tica
// Autores: Clara Rubio Almagro y Antonio Pe�a Castillo
//
// Este c�digo est� basado en el c�digo FlagEventos de empotrados
//
//*****************************************************************************

// LIBRER�AS ***
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h> 			 // rand()
#include "inc/hw_memmap.h"       // TIVA: Definiciones del mapa de memoria
#include "inc/hw_types.h"        // TIVA: Definiciones API
#include "inc/hw_ints.h"         // TIVA: Definiciones para configuracion de interrupciones
#include "driverlib/gpio.h"      // TIVA: Funciones API de GPIO
#include "driverlib/pin_map.h"   // TIVA: Mapa de pines del chip
#include "driverlib/rom.h"       // TIVA: Funciones API incluidas en ROM de micro (MAP_)
#include "driverlib/rom_map.h"   // TIVA: Mapeo automatico de funciones API incluidas en ROM de micro (MAP_)
#include "driverlib/sysctl.h"    // TIVA: Funciones API control del sistema
#include "driverlib/uart.h"      // TIVA: Funciones API manejo UART
#include "driverlib/interrupt.h" // TIVA: Funciones API manejo de interrupciones
#include "utils/uartstdio.h"     // TIVA: Funciones API UARTSTDIO (printf)
#include "drivers/buttons.h"     // TIVA: Funciones API manejo de botones
#include "drivers/rgb.h"         // TIVA: Funciones API manejo de botones
#include "FreeRTOS.h"            // FreeRTOS: definiciones generales
#include "task.h"                // FreeRTOS: definiciones relacionadas con tareas
#include "semphr.h"              // FreeRTOS: definiciones relacionadas con semaforos
#include "event_groups.h"        // FreeRTOS: definiciones relacionadas con grupos de eventos
#include "driverlib/pwm.h"
#include "inc/hw_ints.h"
#include "inc/hw_adc.h"
#include "driverlib/adc.h"
#include "drivers/configADC.h"

// COLAS ***
extern QueueHandle_t cola_adc1;
QueueSetHandle_t grupo_colas;
QueueHandle_t cola_adc1;
QueueHandle_t cola_parao;
QueueHandle_t cola_avanza;
QueueHandle_t cola_girar;
QueueHandle_t cola_remolino;

// VARIABLES FLAGS DE EVENTOS ***
static EventGroupHandle_t FlagsEventos;
EventGroupHandle_t FlagsTareas, FlagsEstados;

// DEFINICI�N FLAGS DE EVENTOS ***
#define WHISKER_FLAG 1 << 0         // Si se activa es porque el whisker ha sido pulsado
#define ENC_RIGHT_FLAG 1 << 1       // Flag del encoder derecho
#define ENC_LEFT_FLAG 1 << 2        // Flag del encoder izquierdo
#define PARA_MOVIMIENTO_FLAG 1 << 3 // Se activa cuando se debe parar el movimiento que est� haciendo de golpe
#define EVENTO_LINEA 1 << 4           // Se activa cuando el robot ha tocado la linea
#define EVENTO_INICIO 1 << 5
#define EVENTO_VISTO 1 << 6
#define EVENTO_LINEA_IZQUIERDA 1 << 7
#define EVENTO_LINEA_DERECHA 1 << 8
#define EVENTO_LINEA_TRASERA 1 << 9


// DEFINICION ESTADOS
#define ESTADO_BUSCANDO_OPONENTE 0
#define ESTADO_ATAQUE_OPONENTE 1
#define ESTADO_TOQUE_LINEA 2
#define ESTADO_INICIAL 3


#define PERIOD_PWM 50               // Ciclos de reloj para conseguir una señal periódica de 50Hz (según reloj de periférico usado)

// ADC SHARP ***
unsigned short Vol[]={349,356,367,376,400,409,426,465,499,531,568,599,624,682,717,849,932,1101,1280,1516};
unsigned short Dist[]={48,46,44,42,40,38,36,34,32,30,28,26,24,22,20,18,16,14,12,10};
unsigned short pos;

// GLOBALES ***
uint16_t duty1 = 77,duty2 = 82;
uint32_t val_load;
uint32_t cont_enc_r=0;
uint32_t cont_enc_l=0;
uint8_t posible_rebote = 0;
int status=0;
uint32_t g_ulSystemClock;

// SEM�FOROS ***
SemaphoreHandle_t semaforo_freertos1;
SemaphoreHandle_t semaforo_secuencia;

// TIMERS ***
TimerHandle_t xTimer_antirrebote;
TimerHandle_t xTimer_ADC;

// INTERRUPCIONES ***
void ADCIntHandler(void);

//*****************************************************************************
//
// The error routine that is called if the driver library encounters an error.
//
//*****************************************************************************
#ifdef DEBUG
void
__error__(char *pcFilename, unsigned long ulLine)
{
}

#endif
//*****************************************************************************

//*****************************************************************************

//*****************************************************************************
//
// This hook is called by FreeRTOS when an stack overflow error is detected.
//
//*****************************************************************************
void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName)
{
	//
	// This function can not return, so loop forever.  Interrupts are disabled
	// on entry to this function, so no processor interrupts will interrupt
	// this loop.
	//
	while(1)
	{
	}
}


void vApplicationIdleHook( void )
{
	SysCtlSleep();
	//SysCtlDeepSleep();
}

//*****************************************************************************
//
// FUNCIONES
//
//*****************************************************************************

// Control del array del sharp
unsigned short binary_lookup(unsigned short *A, unsigned short key, unsigned short imin, unsigned short imax)
{
  unsigned int imid;
  while (imin < imax)
  {
      imid= (imin+imax)>>1;

      if ( A[imid] < key)
      {
          imin = imid + 1;
      }
      else
      {
        imax = imid - 1;
      }
  }
  return imax;    //Al final imax=imin y en dicha posicion hay un numero mayor o igual que el buscado
}

//*****************************************************************************
//
// TAREAS
//
//*****************************************************************************

// Tarea que parpadea el LED verde un numero aleatorio de veces
static portTASK_FUNCTION(TareaUnica,pvParameters)
{
    int16_t MuestraLeida = 15;
	while(1)
	{
		//Espera a que se active el flag WHISKER_FLAG
		// Al activarse, lo borra y continua
	    EventBits_t tarea = xEventGroupWaitBits(FlagsEventos,WHISKER_FLAG,pdTRUE,pdFALSE,portMAX_DELAY);
	    if(tarea == WHISKER_FLAG)
	    {
	        MuestraLeida = 15;
	        //xQueueSend(cola_avanza,&MuestraLeida,portMAX_DELAY);
	        //vTaskDelay(100);
	        /*xEventGroupSetBits(FlagsEventos, PARA_MOVIMIENTO_FLAG);
	        MuestraLeida = 90;
	        xQueueSend(cola_girar,&MuestraLeida,portMAX_DELAY);
	        xQueueSend(cola_remolino,&MuestraLeida,portMAX_DELAY);
	        MuestraLeida = -90;
	        xQueueSend(cola_remolino,&MuestraLeida,portMAX_DELAY);
	        MuestraLeida = -15;
            xQueueSend(cola_avanza,&MuestraLeida,portMAX_DELAY);
            xQueueSend(cola_parao,&MuestraLeida,portMAX_DELAY);
            vTaskDelay(10000);
            MuestraLeida = -90;
            xQueueSend(cola_girar,&MuestraLeida,portMAX_DELAY);*/
	    }
	}
}

// Tarea de control de movimiento
static portTASK_FUNCTION(TareaMovimiento,pvParameters)
{
    QueueSetMemberHandle_t Active;
    EventBits_t tarea;
    uint16_t angulo;
    int16_t muestra;                    // Variable que guarda lo mandado por las colas
    uint16_t numPest;                   // Numero de pesta�as que debe recorrer el robot para realizar el movimiento

    while(1)
    {
        // Se bloquea esperando alguna cola
        Active = xQueueSelectFromSet(grupo_colas,portMAX_DELAY);

        // Cada cola coge el sem�foro para tener uso exclusivo de los motores hasta que acaben su movimiento
        xQueueReceive(cola_parao,&muestra,0);
        xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
        // Identifica que cola ha sido usada
        if(Active == cola_parao)
        {
            xQueueReceive(cola_parao,&muestra,0);
        }
        else if (Active == cola_avanza)
        {
            xQueueReceive(cola_avanza,&muestra,0);

            // Si recibe una muestra negativa retrocede
            if(muestra < 0)
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                muestra = muestra * (-1);
                angulo = muestra/3;
                numPest = angulo/0.52;

                duty1 = 65;
                duty2 = 95;
            }
            else
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                angulo = muestra/3;
                numPest = angulo/0.52;

                duty1 = 95;
                duty2 = 65;
            }

            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);

            // Espera a que los encoders hayan captado todas las pesta�as que deben haber recorrido
            // o a que se le obligue a parar el movimiento al instante
            while(numPest > 0)
            {
                tarea = xEventGroupWaitBits(FlagsEventos,ENC_RIGHT_FLAG|PARA_MOVIMIENTO_FLAG,pdTRUE,pdFALSE,portMAX_DELAY);
                if(tarea == ENC_RIGHT_FLAG)
                {
                    numPest--;
                }
                else if(tarea == PARA_MOVIMIENTO_FLAG)
                {
                    numPest = 0;
                }
            }
        }
        else if (Active == cola_girar)
        {
            xQueueReceive(cola_girar,&muestra,0);

            // Si recibe una muestra negativa gira en el otro sentido
            if(muestra < 0)
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                muestra = muestra * (-1);
                angulo = (muestra*10)/3;
                numPest = angulo/30;

                duty1 = 81;
                duty2 = 87;
            }
            else
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                angulo = (muestra*10)/3;
                numPest = angulo/30;

                duty1 = 81;
                duty2 = 76;
            }

            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);

            // Espera a que los encoders hayan captado todas las pesta�as que deben haber recorrido
            // o a que se le obligue a parar el movimiento al instante
            while(numPest > 0)
            {
                tarea = xEventGroupWaitBits(FlagsEventos,ENC_RIGHT_FLAG|PARA_MOVIMIENTO_FLAG,pdTRUE,pdFALSE,portMAX_DELAY);
                if(tarea == ENC_RIGHT_FLAG)
                {
                    numPest--;
                }
                else if(tarea == PARA_MOVIMIENTO_FLAG)
                {
                    numPest = 0;
                }
            }
        }
        else if (Active == cola_remolino)
        {
            xQueueReceive(cola_remolino,&muestra,0);

            // Si recibe una muestra negativa gira en el otro sentido
            if(muestra < 0)
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                muestra = muestra * (-1);
                angulo = (muestra*10)/3;
                numPest = angulo/60;

                duty1 = 87;
                duty2 = 86;
            }
            else
            {
                // Calcula el numero de pesta�as que debe recorrar para cumplir el movimiento
                angulo = (muestra*10)/3;
                numPest = angulo/60;

                duty1 = 76;
                duty2 = 77;
            }

            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
            PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);

            // Espera a que los encoders hayan captado todas las pesta�as que deben haber recorrido
            // o a que se le obligue a parar el movimiento al instante
            while(numPest > 0)
            {
                tarea = xEventGroupWaitBits(FlagsEventos,ENC_RIGHT_FLAG|PARA_MOVIMIENTO_FLAG,pdTRUE,pdFALSE,portMAX_DELAY);
                if(tarea == ENC_RIGHT_FLAG)
                {
                    numPest--;
                }
                else if(tarea == PARA_MOVIMIENTO_FLAG)
                {
                    numPest = 0;
                }
            }
        }

        // Cada movimiento acaba parando
        /*duty1 = 81;
        duty2 = 82;
        PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
        PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);*/

        // Suelto el uso exclusivo de movimiento
        xSemaphoreGive(semaforo_freertos1);
    }

}

// Tarea de control del sharp
// Recibe los datos mediante una cola de forma peri�dica
static portTASK_FUNCTION(TareaADC,pvParameters)
{

    uint32_t MuestraRecibida;
    unsigned short* A;
    A=&Vol[0];

    while(1)
    {

        xQueueReceive(cola_adc1,&MuestraRecibida,portMAX_DELAY);
        pos=binary_lookup(A,MuestraRecibida,0,(unsigned short)(sizeof(Vol)/sizeof(Vol[0])));

        if (pos > 2 && pos < 15)
        {
            xEventGroupSetBits(FlagsEstados, EVENTO_VISTO);
        }
        /*if(pos<3)
        {

        } else if(pos>=3  && pos< 10)
        {

        } else if(pos>=10  && pos< 15)
        {

        }
        else if(pos>=15)
        {

        }*/

    }
}

// Tarea de la maquina de estados que determina el funcionamiento
// en cada momento del robot.
static portTASK_FUNCTION(TareaMakinaEstados,pvParameters)
{
    uint8_t estado = 3;
    int16_t movimiento;
    while(1)
    {
        // Espera un evento
        EventBits_t evento = xEventGroupWaitBits(FlagsEstados,EVENTO_INICIO|EVENTO_VISTO|EVENTO_LINEA_DERECHA|EVENTO_LINEA_IZQUIERDA|EVENTO_LINEA_TRASERA,pdTRUE,pdFALSE,portMAX_DELAY);

        switch(estado)
        {
        case ESTADO_INICIAL:
            //xQueueSend(cola_parao,&movimiento,portMAX_DELAY);
            if(evento == EVENTO_INICIO)
            {
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                estado = ESTADO_BUSCANDO_OPONENTE;
                duty1 = 90;
                duty2 = 90;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }
            break;
        case ESTADO_BUSCANDO_OPONENTE:
            if(evento == EVENTO_VISTO)
            {
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                estado = ESTADO_ATAQUE_OPONENTE;
                duty1 = 64;
                duty2 = 87;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }
            else if(evento == EVENTO_LINEA_DERECHA || evento == EVENTO_LINEA_IZQUIERDA)
            {
                estado = ESTADO_TOQUE_LINEA;
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                estado = ESTADO_BUSCANDO_OPONENTE;

                duty1 = 94;
                duty2 = 66;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }
            else if( evento == EVENTO_LINEA_TRASERA)
            {
                estado = ESTADO_TOQUE_LINEA;
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                duty1 = 95;
                duty2 = 65;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }
            break;
        case ESTADO_ATAQUE_OPONENTE:
            if(evento == EVENTO_LINEA_DERECHA || evento == EVENTO_LINEA_IZQUIERDA )
            {
                estado = ESTADO_TOQUE_LINEA;
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                duty1 = 95;
                duty2 = 65;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }
            else if( evento == EVENTO_LINEA_TRASERA)
            {
                estado = ESTADO_TOQUE_LINEA;
                xSemaphoreTake(semaforo_freertos1,portMAX_DELAY);
                duty1 = 65;
                duty2 = 95;
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
                PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000);
                xSemaphoreGive(semaforo_freertos1);
            }

            break;
        case ESTADO_TOQUE_LINEA:
            break;
        }

    }
}

//*****************************************************************************
//
// MANEJADORES DE TIMERS
//
//*****************************************************************************

// Funci�n callback del timer antirrebote que pone posible_rebote
// a cero para indicar que ya no hay peligro de rebote y se pueden
// volver a tomar datos reales del whisker
void vTimerCallback_rebote(TimerHandle_t timer)
{
    posible_rebote = 0;
}

// Funci�n callback del adc que funciona como un trigger para
// captar la informaci�n
void vTimerCallback_ADC(TimerHandle_t timer)
{
    ADCProcessorTrigger(ADC1_BASE,3);
    xTimerReset(xTimer_ADC, portMAX_DELAY);
}

//*****************************************************************************
//
// MAIN
//
//*****************************************************************************
int main(void)
{

	//
	// Set the clocking to run at 40 MHz from the PLL.
	//
	MAP_SysCtlClockSet(SYSCTL_SYSDIV_5 | SYSCTL_USE_PLL | SYSCTL_XTAL_16MHZ |
			SYSCTL_OSC_MAIN);

	// INICIALIZACI�N MOTORES ***
    uint32_t pwm_clk;
    SysCtlPWMClockSet(SYSCTL_PWMDIV_64);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_PWM1);     // Habilita modulo PWM
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOF);    // Habilita puerto salida para se�al PWM (ver en documentacion que pin se corresponde a cada m�dulo PWM)
    GPIOPinTypePWM(GPIO_PORTF_BASE, GPIO_PIN_3);
    GPIOPinTypePWM(GPIO_PORTF_BASE, GPIO_PIN_2);
    GPIOPinConfigure(GPIO_PF3_M1PWM7);
    GPIOPinConfigure(GPIO_PF2_M1PWM6);

    pwm_clk = SysCtlClockGet() / 64;
    val_load = (pwm_clk/ PERIOD_PWM) - 1;

    PWMGenConfigure(PWM1_BASE, PWM_GEN_3, PWM_GEN_MODE_DOWN);    // M�dulo PWM contara hacia abajo
    PWMGenPeriodSet(PWM1_BASE, PWM_GEN_3, val_load);
    PWMPulseWidthSet(PWM1_BASE, PWM_OUT_7, duty1*val_load/1000);
    PWMPulseWidthSet(PWM1_BASE, PWM_OUT_6, duty2*val_load/1000); // Establece el periodo (en este caso, un porcentaje del valor m�ximo)
    PWMOutputState(PWM1_BASE, PWM_OUT_7_BIT, true);
    PWMOutputState(PWM1_BASE, PWM_OUT_6_BIT, true);              // Habilita la salida de la se�al
    PWMGenEnable(PWM1_BASE, PWM_GEN_3);                          // Habilita/pone en marcha el generador PWM

    // Get the system clock speed.
    g_ulSystemClock = SysCtlClockGet();

    // INICIALIZACI�N WHISKER Y SU INTERRUPCI�N ***
    ButtonsInit();
    GPIOIntTypeSet(GPIO_PORTF_BASE, ALL_BUTTONS,GPIO_FALLING_EDGE);
    GPIOIntEnable(GPIO_PORTF_BASE,ALL_BUTTONS);
    IntEnable(INT_GPIOF);

    // CONFIGURACI�N INFRARROJOS ***
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOD);
    SysCtlPeripheralSleepEnable(SYSCTL_PERIPH_GPIOD);
    GPIOPinTypeGPIOInput(GPIO_PORTD_BASE, GPIO_PIN_0|GPIO_PIN_2 | GPIO_PIN_3);
    GPIOIntTypeSet(GPIO_PORTD_BASE, GPIO_PIN_0|GPIO_PIN_2 | GPIO_PIN_3,GPIO_RISING_EDGE);
    IntPrioritySet(INT_GPIOD,configMAX_SYSCALL_INTERRUPT_PRIORITY);
    GPIOIntEnable(GPIO_PORTD_BASE,GPIO_PIN_0|GPIO_PIN_2 | GPIO_PIN_3);
    IntEnable(INT_GPIOD);

    // CONFIGURACI�N ADC ***
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOA);
    MAP_GPIOPinTypeGPIOInput(GPIO_PORTA_BASE,GPIO_PIN_2 | GPIO_PIN_3);
    GPIOIntEnable(GPIO_PORTA_BASE,GPIO_PIN_2 | GPIO_PIN_3);
    IntEnable(INT_GPIOA);

    SysCtlPeripheralEnable(SYSCTL_PERIPH_ADC1);
    SysCtlPeripheralSleepEnable(SYSCTL_PERIPH_ADC1);
    IntPrioritySet(INT_ADC1SS3,configMAX_SYSCALL_INTERRUPT_PRIORITY);
    IntEnable(INT_ADC1SS3);
    ADCIntClear(ADC1_BASE,3);
    ADCIntEnable(ADC1_BASE,3);
    ADCIntRegister(ADC1_BASE, 3, ADCIntHandler);
    ADCSequenceDisable(ADC1_BASE,3);
    ADCSequenceConfigure(ADC1_BASE,3,ADC_TRIGGER_PROCESSOR,0);                      // Disparo por evento Timer (timer trigger)
    ADCSequenceStepConfigure(ADC1_BASE,3,0,ADC_CTL_CH8|ADC_CTL_IE |ADC_CTL_END);
    ADCSequenceEnable(ADC1_BASE,3);                                                 // ACTIVO LA SECUENCIA

    // CREACI�N COLAS **********************************************

    // Cola del adc del sharp
    cola_adc1=xQueueCreate(8,sizeof(uint32_t));
    if (cola_adc1==NULL)
    {
        while(1);
    }

    // Cola que controla si debe estar parado
    cola_parao=xQueueCreate(8,sizeof(uint32_t));
    if (cola_parao==NULL)
    {
        while(1);
    }

    // Cola que controla cuanto debe avanzar o retroceder
    cola_avanza=xQueueCreate(8,sizeof(uint32_t));
    if (cola_avanza==NULL)
    {
        while(1);
    }

    // Cola que controla cuanto debe girar
    cola_girar=xQueueCreate(8,sizeof(uint32_t));
    if (cola_girar==NULL)
    {
        while(1);
    }

    // Cola que controla cuanto debe girar sobre si mismo
    cola_remolino=xQueueCreate(8,sizeof(uint32_t));
    if (cola_remolino==NULL)
    {
        while(1);
    }

    // CREACI�N DE TAREAS **********************************************

	// Creaci�n de tarea de control
	if (xTaskCreate( TareaUnica, "TUnica", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY+1, NULL )!=pdPASS)
		while (1);

	// Creaci�n de tarea de control de adc
    if (xTaskCreate( TareaADC, "ADC", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY+1, NULL )!=pdPASS)
            while (1);

    // Creaci�n de tarea de control de movimiento
    if (xTaskCreate( TareaMovimiento, "Movimiento", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY+1, NULL )!=pdPASS)
            while (1);

    // Creaci�n de tarea de control de funcionamiento completo del robot por medio de una maquina de estados
    if (xTaskCreate( TareaMakinaEstados, "MaquinaEstados", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY+1, NULL )!=pdPASS)
            while (1);

    // FLAGS, TIMERS Y SEM�FOROS ****************************************

	// Crea el grupo de eventos
	FlagsEventos = xEventGroupCreate();
	if( FlagsEventos == NULL )
	{
		while(1);
	}

	FlagsTareas = xEventGroupCreate();
	if( FlagsTareas == NULL )
	{
	    while(1);
	}

	FlagsEstados = xEventGroupCreate();
    if( FlagsEstados == NULL )
    {
        while(1);
    }

	// Crea el sem�foro de control de movimiento de los motores
	 semaforo_freertos1=xSemaphoreCreateBinary();
	 if ((semaforo_freertos1==NULL))
	 {
	     while (1); //No hay memoria para los semaforos
	 }
	 xSemaphoreGive(semaforo_freertos1);

     // Crea el timer de control antirrebote del whisker
     xTimer_antirrebote = xTimerCreate("TimerSW2",0.5 * configTICK_RATE_HZ, pdFALSE,NULL,vTimerCallback_rebote);
     if( xTimer_antirrebote == NULL )
     {
          /* The timer was not created. */
          while(1);
     }

     // Crea el timer de control del adc
     xTimer_ADC = xTimerCreate("TimerSW3",0.2 * configTICK_RATE_HZ, pdFALSE,NULL,vTimerCallback_ADC);
     if( xTimer_ADC == NULL )
     {
          /* The timer was not created. */
          while(1);
     }

     // Crea grupo de colas y a�ade las existentes
     xTimerStart(xTimer_ADC, portMAX_DELAY);
     grupo_colas = xQueueCreateSet( 16+16+16);
     if(grupo_colas==NULL)
     {
         while(1);
     }
     if(xQueueAddToSet(cola_parao,grupo_colas)!=pdPASS)
    {
      while(1);
    }
     if(xQueueAddToSet(cola_avanza,grupo_colas)!=pdPASS)
    {
      while(1);
    }
     if(xQueueAddToSet(cola_girar,grupo_colas)!=pdPASS)
    {
      while(1);
    }
     if(xQueueAddToSet(cola_remolino,grupo_colas)!=pdPASS)
    {
      while(1);
    }

	//
	// Start the scheduler.  This should not return.
	//
	vTaskStartScheduler();	//el RTOS habilita las interrupciones al entrar aqui, asi que no hace falta habilitarlas

	//
	// In case the scheduler returns for some reason, print an error and loop
	// forever.
	//

	while(1)
	{
	}
}

//*****************************************************************************
//
// INTERRUPCIONES
//
//*****************************************************************************

// Interrupci�n de control del whisker
void GPIOFIntHandler(void)
{
	BaseType_t xHigherPriorityTaskWoken=pdFALSE;
	int32_t i32PinStatus=MAP_GPIOIntStatus(GPIO_PORTF_BASE,ALL_BUTTONS);

	// Solo puede activar la flag cuando no haya peligro de rebote
	if ((i32PinStatus & WHISKER) && !posible_rebote)
    {
	    //Activa WHISKER_FLAG
    	xEventGroupSetBitsFromISR(FlagsEstados, WHISKER_FLAG, &xHigherPriorityTaskWoken );
    	posible_rebote = 1;                     // Aviso de que lo recibido puede ser un rebote
    	xTimerStart(xTimer_antirrebote, 0);     // Activo el timer de control de rebotes
    }
	else if(i32PinStatus & RIGHT_BUTTON)
	{
	    xEventGroupSetBitsFromISR(FlagsEstados, EVENTO_INICIO, &xHigherPriorityTaskWoken );
	}

	MAP_GPIOIntClear(GPIO_PORTF_BASE,ALL_BUTTONS);
	portEND_SWITCHING_ISR(xHigherPriorityTaskWoken);
}

// Interrupci�n de control de los encoders
void GPIOAIntHandler(void)
{
    BaseType_t xHigherPriorityTaskWoken=pdFALSE;
    int32_t i32PinStatus=MAP_GPIOIntStatus(GPIO_PORTA_BASE,GPIO_PIN_2|GPIO_PIN_3);

    // Activo la flag del encoder que se haya activado
    if (i32PinStatus & GPIO_PIN_2)
    {
        xEventGroupSetBitsFromISR(FlagsEventos, ENC_RIGHT_FLAG, &xHigherPriorityTaskWoken );
    }
    if (i32PinStatus & GPIO_PIN_3)
    {
        xEventGroupSetBitsFromISR(FlagsEventos, ENC_LEFT_FLAG, &xHigherPriorityTaskWoken );
    }

    MAP_GPIOIntClear(GPIO_PORTA_BASE,GPIO_PIN_2|GPIO_PIN_3);
    portEND_SWITCHING_ISR(xHigherPriorityTaskWoken);
}

// Interrupci�n de control de los encoders
void GPIODIntHandler(void)
{
    BaseType_t xHigherPriorityTaskWoken=pdFALSE;
    int32_t i32PinStatus=MAP_GPIOIntStatus(GPIO_PORTD_BASE,GPIO_PIN_0|GPIO_PIN_2|GPIO_PIN_3);

    // Activo la flag del encoder que se haya activado
    if (i32PinStatus & GPIO_PIN_0)
    {
        xEventGroupSetBitsFromISR(FlagsEstados, EVENTO_LINEA_IZQUIERDA, &xHigherPriorityTaskWoken );
    }
    else if (i32PinStatus & GPIO_PIN_2)
    {
        xEventGroupSetBitsFromISR(FlagsEstados, EVENTO_LINEA_DERECHA, &xHigherPriorityTaskWoken );
    }
    else if (i32PinStatus & GPIO_PIN_3)
    {
        xEventGroupSetBitsFromISR(FlagsEstados, EVENTO_LINEA_TRASERA, &xHigherPriorityTaskWoken );
    }

    MAP_GPIOIntClear(GPIO_PORTD_BASE,GPIO_PIN_0|GPIO_PIN_2|GPIO_PIN_3);
    portEND_SWITCHING_ISR(xHigherPriorityTaskWoken);
}

// Interrupci�n de control de adc
void ADCIntHandler(void)
{
    portBASE_TYPE higherPriorityTaskWoken=pdFALSE;
    uint32_t MuestraLeida;
    ADCSequenceDataGet(ADC1_BASE,3,&MuestraLeida);                          //COGEMOS LOS DATOS GUARDADOS
    xQueueSendFromISR(cola_adc1,&MuestraLeida,&higherPriorityTaskWoken);    //Guardamos en la cola y enviamos
    ADCIntClear(ADC1_BASE,3);
    portEND_SWITCHING_ISR(higherPriorityTaskWoken);
}

